-- Prove2me | Definitions.Def_FewInnerTSP_CrossingChoices
-- name    : FewInnerTSP_CrossingChoices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:30.798643+00:00
-- url     : https://prove2.me/theorems/0cf286f6-8bba-447f-9245-20d33d004da8
-- title:
--   Separators, straddling edges, CrossingChoices (Algorithm 1) and child states
-- statement:
--   A **separator choice** is a center $c$, a balancing side $u$ and a parameter $t$; the separator $\sigma$ is the closed axis-aligned square with center $c$ and side $tu$. Normalized coordinates are $(x-c)/u$.
--
--   1. An edge is **endpoint-straddling** if one endpoint lies in $\sigma$ and the other outside; a segment with both endpoints outside is never split.
--   2. The **owner** of a free edge is its core endpoint of least label. A free edge is **long** if its length exceeds $u$, and lies in the **medium bucket** $(j,i,\ell)$ if its length is in $(2^{-j-1}u,2^{-j}u]$ and its owner's normalized position lies in grid cell $(i,\ell)$ of scale $2^{-j}$.
--   3. **CrossingChoices** (Algorithm 1) on a state for $\sigma$ is the family of sets $\mathrm{Sel}\subseteq E$ of straddling edges with at most $\lambda$ long free edges, at most $\lambda$ edges in each medium bucket, every mandatory straddling edge, and degree at most $r(v)$ at every vertex, where $\lambda=400p_0$.
--   4. The **residual test** of §5.3 rejects $\mathrm{Sel}$ if a vertex saturated by $\mathrm{Sel}$ ($r'(v)=0$) is incident to a mandatory edge not in $\mathrm{Sel}$.
--   5. The **child state** on one side keeps the vertices of that side with $r'(v)>0$, has as terminals exactly those with $r'(v)=1$, and inherits the allowed and mandatory edges with both endpoints kept, with their identities and weights.
--
--   **Formalization Note** The family is written as a filter of the subsets of $E$; Theorem 4.1 is about how fast a program enumerates it. The page lists buckets down to scale $2^{-J}$; here every length class is capped, which loses no witness.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §4, p.5 (PDF p.7); Algorithm 1 and App. B.4, p.18 (PDF p.20); §5.3, p.10 (PDF p.12); App. F, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_FewInnerTSP_State
import Definitions.Def_FewInnerTSP_Charges

namespace FewInnerTSP

/-- **The separator of one call**: the center `c` and side `u` of the balancing square and the parameter
`t`. The separator `σ` is the closed square with center `c` and side `t * u`.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), §4.1, p.6 (PDF p.8). -/
structure SepChoice where
  c : Pt
  u : ℝ
  t : ℝ

/-- The separator square of a choice. -/
def SepChoice.square (σ : SepChoice) : Set Pt := closedSquare σ.c (σ.t * σ.u)

/-- The normalized coordinates of a point: center `0`, balancing side `1`.
Source: Li, Ma, Gong, App. B.1, p.16 (PDF p.18). -/
noncomputable def SepChoice.normalize (σ : SepChoice) (x : Pt) : Pt :=
  !₂[(x 0 - σ.c 0) / σ.u, (x 1 - σ.c 1) / σ.u]

/-- `e` is **endpoint-straddling** for `σ`: its endpoints belong to different sides of the square.
Source: Li, Ma, Gong, §4, p.5 (PDF p.7). -/
def Straddles {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (σ : SepChoice) (e : Edge n m) : Prop :=
  ∃ a b, Γ.ends e = s(a, b) ∧ P a ∈ σ.square ∧ P b ∉ σ.square

/-- The designated core endpoint of a free edge: its core endpoint of least label.
Source: Li, Ma, Gong, §4.2, p.6 (PDF p.8): "chosen by a fixed label rule". -/
def IsOwner {n : ℕ} (A : Finset (Fin n)) (e : Sym2 (Fin n)) (v : Fin n) : Prop :=
  v ∈ A ∧ v ∈ e ∧ ∀ u ∈ A, u ∈ e → v ≤ u

/-- `e` is a long free edge: its normalized length exceeds `1`.
Source: Li, Ma, Gong, App. B.4, p.18 (PDF p.20). -/
def IsLongFree {n m : ℕ} (P : Fin n → Pt) (σ : SepChoice) (e : Edge n m) : Prop :=
  ∃ f, e = Edge.free f ∧ σ.u < edgeLen P f

/-- `e` is in the medium bucket of the cell `(i, ℓ)` at scale `s = 2^{-j}`: a free edge of normalized
length in `(s/2, s]` whose designated core endpoint lies in that normalized grid cell.
Source: Li, Ma, Gong, App. B.4, p.18 (PDF p.20). -/
def InMediumBucket {n m : ℕ} (P : Fin n → Pt) (A : Finset (Fin n)) (σ : SepChoice) (j : ℕ)
    (i l : ℤ) (e : Edge n m) : Prop :=
  ∃ f, e = Edge.free f ∧ scale (j + 1) * σ.u < edgeLen P f ∧ edgeLen P f ≤ scale j * σ.u ∧
    ∃ v, IsOwner A f v ∧ σ.normalize (P v) ∈ gridCell j i l

open Classical in
/-- **`CrossingChoices` (Algorithm 1)** on the state `S` for the separator `σ`: the sets `Sel ⊆ E` of
endpoint-straddling edges with at most `λ` long free edges, at most `λ` medium free edges in each owner
bucket, all mandatory straddling edges, and the degree caps.
Source: Li, Ma, Gong, Algorithm 1, p.18 (PDF p.20), App. F, p.22 (PDF p.24): "The same cover bounds long
straddling edges".

**Formalization Note** This is the set Algorithm 1 enumerates, written as a filter of the powerset of
`E`; the running time is a separate matter (Theorem 4.1). The page lists buckets only for scales down to
`2^{-J}`; at a separator with clearance (11) no straddling edge has a shorter length class, and the Lean
filter caps all classes. Skeleton edges are listed by the straddling test alone. -/
noncomputable def crossingChoices {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (S : State n m)
    (σ : SepChoice) : Finset (Finset (Edge n m)) :=
  S.E.powerset.filter fun Sel =>
    (∀ e ∈ Sel, Straddles P Γ σ e) ∧
    (Sel.filter (IsLongFree P σ)).card ≤ lam ∧
    (∀ (j : ℕ) (i l : ℤ), (Sel.filter (InMediumBucket P S.A σ j i l)).card ≤ lam) ∧
    (∀ e ∈ S.F, Straddles P Γ σ e → e ∈ Sel) ∧
    (∀ v ∈ S.V, edgeDeg Γ Sel v ≤ S.req v)

/-- The residual test of §5.3 not already in Algorithm 1: a vertex with `r′(v) = 0` is not incident to a
mandatory edge outside `Sel`.
Source: Li, Ma, Gong, §5.3, p.10 (PDF p.12). -/
def PassesResidual {n m : ℕ} (Γ : Skeleton n m) (S : State n m) (Sel : Finset (Edge n m)) : Prop :=
  ∀ v ∈ S.V, edgeDeg Γ Sel v = S.req v → ∀ e ∈ S.F, v ∈ Γ.ends e → e ∈ Sel

open Classical in
/-- **The child state** on the given side (`true` = inside `σ`): the vertices of that side with `r′ > 0`
survive, the terminals are exactly the survivors with `r′ = 1`, and the child inherits the allowed and
mandatory edges with both endpoints surviving, with their identities and weights.
Source: Li, Ma, Gong, §5.3, p.10 (PDF p.12). -/
noncomputable def childState {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (S : State n m)
    (σ : SepChoice) (Sel : Finset (Edge n m)) (side : Bool) : State n m :=
  let keep : Fin n → Prop := fun v =>
    (P v ∈ σ.square ↔ side = true) ∧ edgeDeg Γ Sel v < S.req v
  { A := S.A.filter keep
    H := S.H.filter keep
    B := S.V.filter fun v => keep v ∧ edgeDeg Γ Sel v + 1 = S.req v
    E := S.E.filter fun e => ∀ v ∈ Γ.ends e, keep v
    F := S.F.filter fun e => ∀ v ∈ Γ.ends e, keep v
    w := S.w }

end FewInnerTSP


