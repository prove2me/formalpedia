-- Prove2me | Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
-- name    : PrimalDualLDR_FixedRecourse_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:16.910169+00:00
-- url     : https://prove2.me/theorems/21017089-4988-4084-a237-e0965f2450b7
-- title:
--   Fixed-recourse one-stage stochastic program $\mathcal{SP}$ with polyhedral support (2.1), $M=\mathbb E(\xi\xi^\top)$, strict feasibility (2.9)
-- statement:
--   The data of the one-stage stochastic program with fixed recourse of §2 consist of dimensions $k, n, m, l$, a probability measure $\mathbb P$ on $(\mathbb R^k, \mathfrak B(\mathbb R^k))$, a recourse matrix $A \in \mathbb R^{m\times n}$, matrices $B \in \mathbb R^{m\times k}$ and $C \in \mathbb R^{n\times k}$ defining the right-hand side $b(\xi) = B\xi$ and the cost $c(\xi) = C\xi$, and $W \in \mathbb R^{l\times k}$, $h \in \mathbb R^l$. The program is
--   $$\mathcal{SP}:\qquad \text{minimize}_{x \in \mathcal L^2_{k,n}}\ \mathbb E\big(c(\xi)^\top x(\xi)\big)\quad\text{subject to}\quad A x(\xi) \le b(\xi)\ \ \mathbb P\text{-a.s.}$$
--
--   The **standing assumptions** of §2 are:
--   1. $\Xi := \{\xi \in \mathbb R^k : W\xi \ge h\}$ (2.1a) is the support of $\mathbb P$, and $\Xi$ is nonempty and bounded (a nonempty compact polyhedron);
--   2. (2.1b): $l \ge 2$, $k \ge 1$, $W = (e_1, -e_1, \hat W^\top)^\top$ and $h = (1, -1, 0, \dots, 0)^\top$, so that every $\xi \in \Xi$ has $\xi_1 = 1$;
--   3. the linear hull of $\Xi$ is $\mathbb R^k$.
--
--   The **second-order moment matrix** is
--   $$M := \mathbb E\big(\xi\xi^\top\big),\qquad M_{ij} = \int \xi_i \xi_j \, d\mathbb P(\xi).$$
--
--   $\mathcal{SP}$ is **strictly feasible** (2.9) if there are a tolerance $\varepsilon > 0$ and decision rules $\bar x \in \mathcal L^2_{k,n}$, $\bar s \in \mathcal L^2_{k,m}$ with
--   $$A\bar x(\xi) + \bar s(\xi) = b(\xi)\quad\text{and}\quad \bar s(\xi) \ge \varepsilon e\qquad \mathbb P\text{-a.s.},$$
--   where $e = (1,\dots,1) \in \mathbb R^m$.
--
--   Every statement of the mission is made for one such setting under the standing assumptions.
--
--   **Formalization Note** The standing assumptions are one predicate `Standing`, used as an explicit hypothesis. The form (2.1b) is stated row by row in the 0-based indexing of `Fin l`: row `0` of $W$ is $e_1$ with $h_0 = 1$, row `1` is $-e_1$ with $h_1 = -1$, and $h_i = 0$ for $i \ge 2$; the remaining rows of $W$ (the matrix $\hat W$) are free. The paper says (2.1b) holds "without loss of generality"; it is assumed here because the paper's proofs use it.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, pp. 3–4, (SP), (2.1a), (2.1b), M; p. 9, (2.9)

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic

open MeasureTheory

namespace PrimalDualLDR.FixedRecourse

/-- The data of the one-stage stochastic program `SP` with fixed recourse of §2 (pp. 3–4) of Kuhn,
Wiesemann, Georghiou, Optimization Online 2009/02/2218: dimensions `k, n, m, l`, a probability measure
`P` on `(ℝ^k, 𝔅(ℝ^k))`, the recourse matrix `A ∈ ℝ^{m×n}`, `B ∈ ℝ^{m×k}` (right-hand side
`b(ξ) = Bξ`), `C ∈ ℝ^{n×k}` (cost `c(ξ) = Cξ`), and `W ∈ ℝ^{l×k}`, `h ∈ ℝ^l` describing the
support (2.1). -/
structure Setting where
  k : ℕ
  n : ℕ
  m : ℕ
  l : ℕ
  P : Measure (Fin k → ℝ)
  [isProb : IsProbabilityMeasure P]
  A : Matrix (Fin m) (Fin n) ℝ
  B : Matrix (Fin m) (Fin k) ℝ
  C : Matrix (Fin n) (Fin k) ℝ
  W : Matrix (Fin l) (Fin k) ℝ
  h : Fin l → ℝ

attribute [instance] Setting.isProb

namespace Setting

variable (σ : Setting)

/-- The set `Ξ = {ξ ∈ ℝ^k : Wξ ≥ h}` of (2.1a). -/
def Xi : Set (Fin σ.k → ℝ) := polyhedron σ.W σ.h

/-- The standing assumptions of §2 (pp. 3–4):
1. `Ξ = {Wξ ≥ h}` is the support of `P` (2.1a);
2. `Ξ` is nonempty and bounded (a nonempty compact polyhedron);
3. `W` and `h` have the form (2.1b): `l ≥ 2`, the first row of `W` is `e_1ᵀ`, the second is `−e_1ᵀ`,
   `h = (1, −1, 0, …, 0)` (with `k ≥ 1`, so that `e_1` exists);
4. the linear hull of `Ξ` is `ℝ^k`. -/
def Standing : Prop :=
  IsSupport σ.P σ.Xi ∧ σ.Xi.Nonempty ∧ Bornology.IsBounded σ.Xi ∧
  0 < σ.k ∧ 2 ≤ σ.l ∧
  (∀ i : Fin σ.l,
    (i.val = 0 → σ.W i = e1 σ.k ∧ σ.h i = 1) ∧
    (i.val = 1 → σ.W i = -e1 σ.k ∧ σ.h i = -1) ∧
    (2 ≤ i.val → σ.h i = 0)) ∧
  Submodule.span ℝ σ.Xi = ⊤

/-- The second-order moment matrix `M := E(ξξᵀ)` (p. 4), entrywise `M_{ij} = ∫ ξ_i ξ_j dP`. -/
noncomputable def M : Matrix (Fin σ.k) (Fin σ.k) ℝ :=
  fun i j => ∫ ξ, ξ i * ξ j ∂σ.P

/-- Strict feasibility (2.9) of `SP` (Proposition 4, p. 9): there are `ε > 0` and decision rules
`x̄ ∈ 𝓛²_{k,n}`, `s̄ ∈ 𝓛²_{k,m}` with `A x̄(ξ) + s̄(ξ) = b(ξ)` and `s̄(ξ) ≥ ε e` `P`-almost surely,
where `e = (1, …, 1) ∈ ℝ^m`. -/
def StrictlyFeasible : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ (xbar : (Fin σ.k → ℝ) → (Fin σ.n → ℝ)) (sbar : (Fin σ.k → ℝ) → (Fin σ.m → ℝ)),
    IsL2Rule σ.P xbar ∧ IsL2Rule σ.P sbar ∧
    ∀ᵐ ξ ∂σ.P, σ.A.mulVec (xbar ξ) + sbar ξ = σ.B.mulVec ξ ∧ ∀ i, ε ≤ sbar ξ i

end Setting

end PrimalDualLDR.FixedRecourse


