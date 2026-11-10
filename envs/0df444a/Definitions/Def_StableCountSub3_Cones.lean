-- Prove2me | Definitions.Def_StableCountSub3_Cones
-- name    : StableCountSub3_Cones
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:48:40.735223+00:00
-- url     : https://prove2.me/theorems/7f2d3a30-9ff6-4b4a-8103-28ba214849c7
-- title:
--   Cones, principal cones, supports and support sizes (with $s=\infty$), swaps and 3-cycles
-- statement:
--   For a downset $D$, a man $m$ and a direction (forward $+$ or backward $-$):
--
--   - A **cone** (Definition 3.2) is a downset of the outward order $P^\pm(D)$.
--   - $\rho^\pm_k$ (`kth`) is the $k$-th rotation involving $m$ in the outward order: it lies in $P^\pm(D)$, involves $m$, and exactly $k-1$ other rotations involving $m$ precede it there. It is undefined (`none`) if it does not exist, in particular for $k=0$.
--   - The **principal cones** are $K^+_{m,D}(k)=\{\rho\in\mathcal R\setminus D:\rho\preceq\rho^+_k\}$ and $K^-_{m,D}(k)=\{\rho\in D:\rho^-_k\preceq\rho\}$, undefined when $\rho^\pm_k$ does not exist.
--   - The **support** of a set of rotations is $S(K)=\bigcup_{\rho\in K}M(\rho)$ (Definition 3.3). $S^\pm_{m,D}(k)=S(K^\pm_{m,D}(k))$, undefined when the cone is, and $S^\pm_{m,D}(0)=\{m\}$. The support size $s^\pm_{m,D}(k)=|S^\pm_{m,D}(k)|$ takes values in $\mathbb N\cup\{\infty\}$, with $s^\pm_{m,D}(k)=\infty$ when the $k$-th rotation does not exist.
--   - Execution (§5.1): executing $\rho$ means eliminating it forward and undoing its elimination backward. `Takes dir ρ a b` says that executing $\rho$ gives $a$ the partner $b$ held immediately before. $\rho$ is the **swap** $(a,b)$ if its participants are the distinct men $a,b$ and they exchange partners; it is the **3-cycle** $(a,b,c)$ if its participants are the distinct men $a,b,c$ and $a,b,c$ receive the partners held by $b,c,a$ respectively.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Definitions 3.2–3.3, p. 14 (PDF 16); §5.1, p. 25 (PDF 27)

import Mathlib
import Definitions.Def_StableCountSub3_RotationPoset

open StableMatching

noncomputable section

namespace StableCountSub3

variable {n : ℕ}

/-- Definition 3.2: a cone (for the downset `D`) is a downset of the outward order
`P^dir(D)`: a subset of its ground set closed under going earlier in that order. -/
def IsCone (I : Instance n) (D : Finset (Rot n)) (dir : Dir) (K : Finset (Rot n)) : Prop :=
  K ⊆ carrier I D dir ∧ ∀ ρ ∈ K, ∀ ρ' ∈ carrier I D dir, outLE I dir ρ' ρ → ρ' ∈ K

/-- `ρ` is the `k`-th rotation involving the man `m` in the outward order `P^dir(D)`
(`ρ⁺_k`, `ρ⁻_k` of Definition 3.2): `ρ` lies in `P^dir(D)`, involves `m`, and exactly `k − 1`
other rotations involving `m` precede it in `P^dir(D)`. -/
def IsKth (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) (k : ℕ) (ρ : Rot n) :
    Prop := by
  classical
  exact ρ ∈ carrier I D dir ∧ ρ ∈ mchain I m ∧
    ((carrier I D dir ∩ mchain I m).filter fun ρ' => ρ' ≠ ρ ∧ outLE I dir ρ' ρ).card + 1 = k

open Classical in
/-- `ρ^dir_k` (Definition 3.2): the `k`-th rotation involving `m` in the outward order, or
`none` if it does not exist (in particular for `k = 0`). -/
def kth (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) (k : ℕ) : Option (Rot n) :=
  if h : ∃ ρ, IsKth I D m dir k ρ then some h.choose else none

/-- Definition 3.2: the `k`-th principal cone
`K⁺_{m,D}(k) = {ρ ∈ ℛ \ D : ρ ⪯ ρ⁺_k}`, `K⁻_{m,D}(k) = {ρ ∈ D : ρ⁻_k ⪯ ρ}`;
`none` (undefined) when the `k`-th rotation does not exist. -/
def principalCone (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) (k : ℕ) :
    Option (Finset (Rot n)) := by
  classical
  exact (kth I D m dir k).map fun ρk => (carrier I D dir).filter fun ρ => outLE I dir ρ ρk

/-- Definition 3.3: the support `S(K) = ⋃_{ρ ∈ K} M(ρ)` of a set of rotations. -/
def support (K : Finset (Rot n)) : Finset (Fin n) := by
  classical
  exact K.biUnion participants

/-- Definition 3.3: `S^dir_{m,D}(k) = S(K^dir_{m,D}(k))`, undefined (`none`) when the `k`-th
rotation does not exist, and `S^dir_{m,D}(0) = {m}`. -/
def supp (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : ℕ → Option (Finset (Fin n))
  | 0 => some {m}
  | k + 1 => (principalCone I D m dir (k + 1)).map support

/-- Definition 3.3: the support size `s^dir_{m,D}(k) = |S^dir_{m,D}(k)|`, with
`s^dir_{m,D}(k) = ∞` (`⊤`) when the `k`-th rotation does not exist. -/
def ssize (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) (k : ℕ) : ℕ∞ :=
  match supp I D m dir k with
  | some S => (S.card : ℕ∞)
  | none => ⊤

/-- Executing `ρ` in direction `dir` (eliminating it forward, undoing its elimination
backward) gives the man `a` the partner that the man `b` held immediately before (§5.1).
Forward: `a`'s new pair `(a, w) ∈ μ' \ μ` has `(b, w) ∈ μ \ μ'`; backward the roles of the two
components of `ρ = (μ \ μ', μ' \ μ)` are exchanged. -/
def Takes (dir : Dir) (ρ : Rot n) (a b : Fin n) : Prop :=
  match dir with
  | .fwd => ∃ w, (a, w) ∈ ρ.2 ∧ (b, w) ∈ ρ.1
  | .bwd => ∃ w, (a, w) ∈ ρ.1 ∧ (b, w) ∈ ρ.2

/-- §5.1: executed in direction `dir`, `ρ` is the swap `(a, b)`: its participants are the two
distinct men `a, b`, who exchange partners. -/
def IsSwapOn (dir : Dir) (ρ : Rot n) (a b : Fin n) : Prop := by
  classical
  exact a ≠ b ∧ participants ρ = {a, b} ∧ Takes dir ρ a b ∧ Takes dir ρ b a

/-- §5.1: executed in direction `dir`, `ρ` is the 3-cycle `(a, b, c)`: its participants are the
three distinct men `a, b, c`, and it assigns the partners held by `b, c, a` immediately before
to `a, b, c` respectively. -/
def Is3CycleOn (dir : Dir) (ρ : Rot n) (a b c : Fin n) : Prop := by
  classical
  exact a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ participants ρ = {a, b, c} ∧
    Takes dir ρ a b ∧ Takes dir ρ b c ∧ Takes dir ρ c a

end StableCountSub3


