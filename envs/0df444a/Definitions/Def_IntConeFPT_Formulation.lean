-- Prove2me | Definitions.Def_IntConeFPT_Formulation
-- name    : IntConeFPT_Formulation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:10.055832+00:00
-- url     : https://prove2.me/theorems/f546ac48-1dff-4452-ab88-0f3329aac98f
-- title:
--   Candidate residue tuples, the formulation $K_R(\gamma)$ (3.2a)–(3.2e), its projection $\hat K_R(\gamma)$, the bound $N_\star$ (3.4), and integral descriptions bounded by $U$
-- statement:
--   A **candidate tuple** is $R=(R^{(1)},\dots,R^{(\tau)})$ with $R^{(t)}\subseteq\{0,\dots,2^d-1\}^d$ and $|R^{(t)}|\le2^d$. For each type $t$ and $r\in R^{(t)}$ there is a block $(z^{(t)}_r,w^{(t)}_r,n^{(t)}_r)\in\mathbb R^d\times\mathbb R^k\times\mathbb R$, with $(y^{(t)},v^{(t)})=\sum_{r\in R^{(t)}}(z^{(t)}_r,w^{(t)}_r)$ and $N^{(t)}=\sum_{r\in R^{(t)}}n^{(t)}_r$. For $N_{\max}\in\mathbb Z_{\ge0}$ and a rational budget $\gamma$, the region $K_R(\gamma)$ is given by
--   $$
--   \begin{aligned}
--   &\textstyle\sum_t(y^{(t)},v^{(t)})\in Q, &&(3.2a)\\
--   &(z^{(t)}_r,w^{(t)}_r,n^{(t)}_r)\in C^{(t)}_r\quad(t\in[\tau],\ r\in R^{(t)}), &&(3.2b)\\
--   &((y^{(t)},v^{(t)},N^{(t)}))_{t=1}^{\tau}\in\mathcal A, &&(3.2c)\\
--   &\textstyle\sum_t\sum_{r\in R^{(t)}}n^{(t)}_r\le N_{\max}, &&(3.2d)\\
--   &\textstyle\sum_t\sum_{r\in R^{(t)}}\Phi^{(t)}_r(z^{(t)}_r,w^{(t)}_r,n^{(t)}_r)\le\gamma. &&(3.2e)
--   \end{aligned}
--   $$
--   Its projection is $\hat K_R(\gamma)=\{(z,n):\exists w,\ (z,w,n)\in K_R(\gamma)\}$, and an integer point of it has all $z^{(t)}_r$ and $n^{(t)}_r$ integral.
--
--   The **uniform multiplicity bound** (3.4) is $N_\star=s(s+1)\,s!\,H^s$ with $s=\tau2^d$, $R=sk$ and $H=(R+1)!\,U^{R+1}$.
--
--   An **integral description** of an instance is an integer system $Wy_{\mathrm{agg}}\le c_{\mathrm{agg}}$ on $y_{\mathrm{agg}}=((y^{(t)},v^{(t)},N^{(t)}))_t$ whose solutions are exactly those with $\sum_t(y^{(t)},v^{(t)})\in Q$ and $y_{\mathrm{agg}}\in\mathcal A$, together with integer systems $A^{(t)}x+B^{(t)}u\le b^{(t)}$ with solution sets exactly $P^{(t)}$. It is **bounded by $U$** (for a box $[-M,M]^d$) when all entries and right-hand sides have absolute value at most $U$, and so do $b_i-a_i^\top x$ for every local row and $W_{i,y^{(t)}}x+W_{i,N^{(t)}}$ for every aggregate row, for all integer $x\in[-M,M]^d$ (p.17).
--
--   **Formalization Note** A set $R^{(t)}$ is given as a duplicate-free list so that an algorithm can read it; only the set matters. The sum in (3.2e) is taken in `EReal`; under (3.2b) each summand is finite for a valid instance. The paper's $R$ in (3.4) is named `Rk` in Lean.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §3.3 pp.11–12 ((3.2a)–(3.2e), D_R), §3.6 p.17 ((3.4), W, U)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue

namespace IntConeFPT

open OnlineCRS.Combine

/-- **Tuples `R = (R^(1), …, R^(τ))` of active residue sets** (§3.2–3.3, pp.11–12), each `R^(t)`
listed without repetition.

**Formalization Note.** A set of residues is given as a duplicate-free list so that an algorithm
can receive it on its tape; only the underlying set matters. -/
abbrev Cand (I : Instance) : Type := Fin I.τ → List (Residue I.d)

/-- **Candidate tuples** (Corollary 8, p.11): `R^(t) ⊆ {0, …, 2^d − 1}^d` with `|R^(t)| ≤ 2^d`. -/
def IsCandidate (I : Instance) (R : Cand I) : Prop :=
  ∀ t, (R t).Nodup ∧ (R t).length ≤ 2 ^ I.d

/-- **The variable blocks `(z_r^(t), w_r^(t), n_r^(t))`**, one per type `t` and active residue
`r ∈ R^(t)` (§3.3, p.11). The block at position `i` of `R t` belongs to the residue `(R t).get i`. -/
abbrev Blocks (I : Instance) (R : Cand I) : Type :=
  (t : Fin I.τ) → Fin (R t).length → Pt I.d I.k

/-- **The typewise aggregate `(y^(t), v^(t)) := Σ_{r∈R^(t)} (z_r^(t), w_r^(t))`** (p.12). -/
def blockAgg {I : Instance} {R : Cand I} (ξ : Blocks I R) (t : Fin I.τ) :
    (Fin I.d → ℝ) × (Fin I.k → ℝ) :=
  ∑ i, ((ξ t i).1, (ξ t i).2.1)

/-- **The typewise count `N^(t) := Σ_{r∈R^(t)} n_r^(t)`** (p.12). -/
def blockCount {I : Instance} {R : Cand I} (ξ : Blocks I R) (t : Fin I.τ) : ℝ :=
  ∑ i, (ξ t i).2.2

/-- **The continuous feasible region `K_R(γ)`, (3.2a)–(3.2e)**.
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §3.3, p.12:
(3.2a) `B(y, v) ≤ c`, i.e. `(y, v) = Σ_t (y^(t), v^(t)) ∈ Q`;
(3.2b) `(z_r^(t), w_r^(t), n_r^(t)) ∈ C_r^(t)` for all `t` and `r ∈ R^(t)`;
(3.2c) `((y^(t), v^(t), N^(t)))_{t=1}^τ ∈ A`;
(3.2d) `Σ_t Σ_{r∈R^(t)} n_r^(t) ≤ N_max`;
(3.2e) `Σ_t Σ_{r∈R^(t)} Φ_r^(t)(z_r^(t), w_r^(t), n_r^(t)) ≤ γ`, for a rational budget `γ`.

**Formalization Note.** The sum in (3.2e) is taken in `EReal`; under (3.2b) every summand is
finite for a valid instance (`Φ_r^(t)` is a finite LP value on `C_r^(t)`). -/
def K (I : Instance) (R : Cand I) (Nmax : ℕ) (γ : ℚ) : Set (Blocks I R) :=
  {ξ | (∑ t, blockAgg ξ t) ∈ I.Q ∧
    (∀ t i, ξ t i ∈ I.Cr t ((R t).get i)) ∧
    (fun t => ((blockAgg ξ t).1, (blockAgg ξ t).2, blockCount ξ t)) ∈ I.A ∧
    ∑ t, blockCount ξ t ≤ (Nmax : ℝ) ∧
    ∑ t, ∑ i, I.Phi t ((R t).get i) (ξ t i) ≤ ((γ : ℝ) : EReal)}

/-- **The projected polyhedron `K̂_R(γ) := {(z, n) : ∃ w, (z, w, n) ∈ K_R(γ)}`** (p.12). -/
def Khat (I : Instance) (R : Cand I) (Nmax : ℕ) (γ : ℚ) :
    Set ((t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℝ) × ℝ) :=
  {zn | ∃ ξ ∈ K I R Nmax γ, ∀ t i, (ξ t i).1 = (zn t i).1 ∧ (ξ t i).2.2 = (zn t i).2}

/-- **Integer points of `R^{D_R}`**: every `z_r^(t)` and `n_r^(t)` integral (p.12, "Only the
coordinates in z and n must be integral"). -/
def IsIntegral {I : Instance} {R : Cand I}
    (zn : (t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℝ) × ℝ) : Prop :=
  ∀ t i, (∀ j, ∃ z : ℤ, (zn t i).1 j = z) ∧ ∃ n : ℤ, (zn t i).2 = n

/-- **The uniform multiplicity bound `N⋆`, (3.4)** (§3.6, p.17):
`s := τ 2^d`, `R := s k`, `H := (R + 1)! U^{R+1}`, `N⋆ := s (s + 1) s! H^s`.

**Formalization Note.** The paper's `R` of (3.4) is named `Rk` here (it is not a residue tuple). -/
def Nstar (τ d k U : ℕ) : ℕ :=
  let s := τ * 2 ^ d
  let Rk := s * k
  let H := (Rk + 1).factorial * U ^ (Rk + 1)
  s * (s + 1) * s.factorial * H ^ s

/-- **Integral descriptions of the aggregate constraints and of the local polytopes** (§3.6,
p.17): a system `W y_agg ≤ c_agg` on `y_agg = ((y^(t), v^(t), N^(t)))_{t=1}^τ` with integer entries
(blocks `WY t`, `WV t` and the count column `WN · t` of type `t`), and for each type an integer
system `A^(t) x + B^(t) u ≤ b^(t)` (`LA t`, `LB t`, `Lb t`). -/
structure IntDesc (I : Instance) where
  mW : ℕ
  WY : Fin I.τ → Matrix (Fin mW) (Fin I.d) ℤ
  WV : Fin I.τ → Matrix (Fin mW) (Fin I.k) ℤ
  WN : Matrix (Fin mW) (Fin I.τ) ℤ
  cW : Fin mW → ℤ
  mL : Fin I.τ → ℕ
  LA : (t : Fin I.τ) → Matrix (Fin (mL t)) (Fin I.d) ℤ
  LB : (t : Fin I.τ) → Matrix (Fin (mL t)) (Fin I.k) ℤ
  Lb : (t : Fin I.τ) → Fin (mL t) → ℤ

namespace IntDesc

variable {I : Instance}

/-- Row `i` of `W y_agg`. -/
def aggLHS (D : IntDesc I) (Y : Fin I.τ → Pt I.d I.k) (i : Fin D.mW) : ℝ :=
  ∑ t, ((∑ j, (D.WY t i j : ℝ) * (Y t).1 j) + (∑ j, (D.WV t i j : ℝ) * (Y t).2.1 j)
    + (D.WN i t : ℝ) * (Y t).2.2)

/-- **The integral systems describe the instance**: `W y_agg ≤ c_agg` holds exactly when
`Σ_t (y^(t), v^(t)) ∈ Q` and `y_agg ∈ A` ("Combine the constraints of Q and A into a system",
p.17), and the local system of each type has exactly `P^(t)` as solution set. -/
def Describes (D : IntDesc I) : Prop :=
  (∀ Y : Fin I.τ → Pt I.d I.k,
    (∀ i, D.aggLHS Y i ≤ D.cW i) ↔ ((∑ t, ((Y t).1, (Y t).2.1)) ∈ I.Q ∧ Y ∈ I.A)) ∧
  ∀ t (p : (Fin I.d → ℝ) × (Fin I.k → ℝ)),
    (∀ i, (∑ j, (D.LA t i j : ℝ) * p.1 j) + (∑ j, (D.LB t i j : ℝ) * p.2 j) ≤ D.Lb t i) ↔
      p ∈ I.P t

/-- **`U` bounds all coefficients** (p.17): every entry and right-hand side of the integral
systems has absolute value `≤ U`, and so do the coefficients obtained by substituting an integer
vector `x ∈ [−M, M]^d`: `|b_i − a_iᵀ x| ≤ U` for every local row, and
`|W_{i,y^(t)} x + W_{i,N^(t)}| ≤ U` for the integer-coordinate and count columns of each type
block of `W`. -/
def BoundedBy (D : IntDesc I) (M U : ℕ) : Prop :=
  (∀ t i j, |D.WY t i j| ≤ U) ∧ (∀ t i j, |D.WV t i j| ≤ U) ∧ (∀ i t, |D.WN i t| ≤ U) ∧
  (∀ i, |D.cW i| ≤ U) ∧
  (∀ t i j, |D.LA t i j| ≤ U) ∧ (∀ t i j, |D.LB t i j| ≤ U) ∧ (∀ t i, |D.Lb t i| ≤ U) ∧
  (∀ t i (x : Fin I.d → ℤ), (∀ j, |x j| ≤ M) → |D.Lb t i - ∑ j, D.LA t i j * x j| ≤ U) ∧
  (∀ t i (x : Fin I.d → ℤ), (∀ j, |x j| ≤ M) → |(∑ j, D.WY t i j * x j) + D.WN i t| ≤ U)

end IntDesc

/-- Binary encoding of a candidate tuple: for each type, the number of residues and the residues. -/
def encCand {I : Instance} (R : Cand I) : List Sym :=
  (List.finRange I.τ).flatMap fun t =>
    encNat (R t).length ++ [3] ++ (R t).flatMap fun r => encResidue r

/-- Encoding of the output of Lemma 13: `0` (no integer point) or `1` and, block by block, the
integer `z`, the rational `w` and the count `n`. -/
def encLift {I : Instance} {R : Cand I} :
    Option ((t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ) → List Sym
  | none => [0]
  | some s => [1] ++ (List.finRange I.τ).flatMap fun t =>
      (List.finRange (R t).length).flatMap fun i =>
        encGen (s t i).1 (s t i).2.1 ++ encNat (s t i).2.2 ++ [3]

end IntConeFPT


