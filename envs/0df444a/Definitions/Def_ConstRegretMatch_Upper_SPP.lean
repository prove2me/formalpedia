-- Prove2me | Definitions.Def_ConstRegretMatch_Upper_SPP
-- name    : ConstRegretMatch_Upper_SPP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:55.925326+00:00
-- url     : https://prove2.me/theorems/4da47fc4-179a-4bd7-82da-51a1c5d7af79
-- title:
--   §2.1 and §4.2, pp. 10–12, 19–20 — (SPP), the partition ℳ₊, ℳ₀, 𝒬₊, 𝒬₀, general position (Def. 2.2), the GP gap ϵ (Def. 2.3), the basis ℬ and the dual system
-- statement:
--   For a right-hand side $b\in\mathbb R^n$, consider the linear program
--   $$\max\ r\cdot z\quad\text{s.t.}\quad Mz+s=b,\quad z\in\mathbb R^d_{\ge0},\ s\in\mathbb R^n_{\ge0}.$$
--   With $b=\lambda$ it is the **static-planning problem** (SPP). A pair $(z,s)$ is *feasible* if it satisfies the constraints and *optimal* if moreover $r\cdot z\ge r\cdot z'$ for every feasible $(z',s')$.
--
--   For a pair $(z^*,s^*)$ define the active matches $\mathcal M_+=\{m: z^*_m>0\}$, the redundant matches $\mathcal M_0=\mathcal M\setminus\mathcal M_+$, the under-demanded queues $\mathcal Q_+=\{j: s^*_j>0\}$ and the over-demanded queues $\mathcal Q_0=\mathcal A\setminus\mathcal Q_+$.
--
--   **General position (GP, Definition 2.2).** The network satisfies GP, with witness $(z^*,s^*)$, if $(z^*,s^*)$ is an optimal solution of (SPP), it is the only optimal solution, and it is non-degenerate:
--   $$|\mathcal M_+|+|\mathcal Q_+|=n.$$
--
--   **General position gap (Definition 2.3).**
--   $$\epsilon=\min_{m\in\mathcal M_+} z^*_m\ \wedge\ \min_{j\in\mathcal Q_+} s^*_j .$$
--
--   **Optimal basis (§4.2).** The basis matrix $\mathcal B$ has the columns of $M$ indexed by $\mathcal M_+$ followed by the unit columns $e_j$, $j\in\mathcal Q_+$; the basic part of $(z^*,s^*)$ is $(z^*_{\mathcal M_+},s^*_{\mathcal Q_+})$.
--
--   **Dual system.** A vector $\theta\in\mathbb R^n$ satisfies the complementary-slackness equations of the basis if
--   $$\theta_j=0\ (j\in\mathcal Q_+),\qquad \sum_i M_{im}\theta_i=r_m\ (m\in\mathcal M_+),$$
--   i.e. $\theta^\top\mathcal B=(r_{\mathcal M_+},0)$. Under GP its unique solution is the paper's $\theta=\sum_{m\in\mathcal M_+}r_my^m$, where $y^m$ are the rows of $\mathcal B^{-1}$.
--
--   These are the structural objects of §4 that the optimality test, the dual weights of the Lyapunov function $h^*$, and the delay $\tau=\lceil\kappa\epsilon^{-1}\rceil$ are built from.
--
--   **Formalization Note** The LP is defined for a general right-hand side; (SPP) is the case `b = lam`. The paper's assumption "without loss of generality $\mathcal M_+=\{1,\dots,d-\varrho\}$" is replaced by indexing the columns of $\mathcal B$ by the sum type $\mathcal M_+\oplus\mathcal Q_+$; no matrix inverse is defined, so no junk inverse can enter a statement (statements that need $Y=\mathcal B^{-1}$ quantify over two-sided inverses). The gap `gpGap` is the minimum of the finite set of positive basic values; under GP and $\sum_i\lambda_i=1$ this set is nonempty, and every statement that mentions `gpGap` assumes both, so its fallback value $0$ is never used.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 10–12, (SPP), Definitions 2.2–2.3; pp. 19–20, §4.2

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network

namespace ConstRegretMatch.Upper

variable {n d : ℕ}

/-- Feasibility for the static-planning problem with a general right-hand side `b`:
`z ≥ 0`, `s ≥ 0` and `M z + s = b`. The paper's (SPP) (§2.1, p. 10) is `b = λ`. -/
def SPPFeasible (N : MatchingNetwork n d) (b : Fin n → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ) :
    Prop :=
  (∀ m, 0 ≤ z m) ∧ (∀ i, 0 ≤ s i) ∧ ∀ i, ∑ m, N.M i m * z m + s i = b i

/-- `(z, s)` is an optimal solution of `max r · z s.t. M z + s = b, z ≥ 0, s ≥ 0`: it is feasible
and its objective is at least that of every feasible `(z', s')`. -/
def SPPOptimal (N : MatchingNetwork n d) (r : Fin d → ℝ) (b : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) : Prop :=
  SPPFeasible N b z s ∧
    ∀ z' s', SPPFeasible N b z' s' → ∑ m, r m * z' m ≤ ∑ m, r m * z m

/-- The active matches `ℳ₊ = {m : z_m > 0}` (§2.1, p. 10). -/
noncomputable def Mplus (z : Fin d → ℝ) : Finset (Fin d) := Finset.univ.filter (fun m => 0 < z m)

/-- The redundant matches `ℳ₀ = ℳ \ ℳ₊`. -/
noncomputable def Mzero (z : Fin d → ℝ) : Finset (Fin d) := Finset.univ.filter (fun m => ¬ 0 < z m)

/-- The under-demanded queues `𝒬₊ = {j : s_j > 0}`. -/
noncomputable def Qplus (s : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (fun j => 0 < s j)

/-- The over-demanded queues `𝒬₀ = 𝒜 \ 𝒬₊`. -/
noncomputable def Qzero (s : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (fun j => ¬ 0 < s j)

/-- The general position condition (GP, Definition 2.2, p. 11) for the network `N`, match values `r`
and arrival rates `lam`, with `(z, s)` its witness: `(z, s)` is an optimal solution of (SPP), it is the
unique optimal solution, and it is non-degenerate, i.e. `|ℳ₊| + |𝒬₊| = n` (p. 11). -/
def IsGP (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) : Prop :=
  SPPOptimal N r lam z s ∧
    (∀ z' s', SPPOptimal N r lam z' s' → z' = z ∧ s' = s) ∧
    (Mplus z).card + (Qplus s).card = n

/-- The positive basic values `{z_m : m ∈ ℳ₊} ∪ {s_j : j ∈ 𝒬₊}`. -/
noncomputable def gapValues (z : Fin d → ℝ) (s : Fin n → ℝ) : Finset ℝ :=
  (Mplus z).image z ∪ (Qplus s).image s

/-- The general position gap (Definition 2.3, pp. 11–12):
`ϵ = min_{m ∈ ℳ₊} z_m ∧ min_{j ∈ 𝒬₊} s_j`, the smallest positive basic value. Under GP with `n ≥ 1`
the set `gapValues z s` has `n` elements counted with multiplicity and is nonempty, so the minimum is
attained; the `else` branch is never reached by a statement of this development (every statement that
mentions `gpGap` assumes GP and `∑ λ_i = 1`, hence `n ≥ 1`). -/
noncomputable def gpGap (z : Fin d → ℝ) (s : Fin n → ℝ) : ℝ :=
  if h : (gapValues z s).Nonempty then (gapValues z s).min' h else 0

/-- Index type of the columns of the optimal basis matrix `ℬ` (§4.2, p. 19): the active matches
`ℳ₊` followed by the under-demanded queues `𝒬₊`. -/
abbrev BasisIdx (z : Fin d → ℝ) (s : Fin n → ℝ) : Type :=
  {m // m ∈ Mplus z} ⊕ {j // j ∈ Qplus s}

/-- The optimal basis matrix `ℬ` (§4.2, p. 19): its columns are the columns of `M` indexed by `ℳ₊`
and the unit columns `e_j` indexed by `j ∈ 𝒬₊` (the columns of the slack variables). -/
noncomputable def basisMatrix (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ) :
    Matrix (Fin n) (BasisIdx z s) ℝ :=
  fun i c => match c with
    | Sum.inl m => N.M i m.1
    | Sum.inr j => if i = j.1 then 1 else 0

/-- The basic part of `(z, s)`: `(z_{ℳ₊}, s_{𝒬₊})`, indexed like the columns of `ℬ`. -/
def basicPart (z : Fin d → ℝ) (s : Fin n → ℝ) : BasisIdx z s → ℝ
  | Sum.inl m => z m.1
  | Sum.inr j => s j.1

/-- The complementary-slackness equations of the dual of (SPP) for the basis of `(z, s)` (§4.2,
p. 20): `θ_j = 0` for `j ∈ 𝒬₊` (the reduced cost of a basic slack vanishes) and
`∑_i M_{im} θ_i = r_m` for `m ∈ ℳ₊` (the reduced cost of a basic match vanishes), i.e.
`θᵀℬ = (r_{ℳ₊}, 0)`. Under GP it has the unique solution `θ = ∑_{m ∈ ℳ₊} r_m y^m`. -/
def IsSPPDual (N : MatchingNetwork n d) (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (θ : Fin n → ℝ) : Prop :=
  (∀ j ∈ Qplus s, θ j = 0) ∧ ∀ m ∈ Mplus z, ∑ i, N.M i m * θ i = r m

end ConstRegretMatch.Upper


