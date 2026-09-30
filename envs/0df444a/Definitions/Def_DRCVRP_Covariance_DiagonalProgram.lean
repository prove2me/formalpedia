-- Prove2me | Definitions.Def_DRCVRP_Covariance_DiagonalProgram
-- name    : DRCVRP_Covariance_DiagonalProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:26:38.47926+00:00
-- url     : https://prove2.me/theorems/537b2536-99fd-4f6a-b34e-a759cca2a6ed
-- title:
--   The one-dimensional program (18) for a diagonal covariance bound
-- statement:
--   Let $S$ be a finite set of customers, $\boldsymbol\sigma\in\mathbb R^n$ with $\sigma_i>0$ (so that the covariance bound is $\Sigma=\operatorname{diag}(\sigma_1^2,\dots,\sigma_n^2)$), $\boldsymbol u\in\mathbb R^n$ (in use, $\boldsymbol u=\boldsymbol q^u$) and $r\in\mathbb R$ (in use, $r=\frac{1-\epsilon}{\epsilon}$). For a parameter $\theta\in\mathbb R$ define
--
--   1. the capped set $S(\theta)=\{i\in S:\ \sigma_i^2>\theta\,u_i\}$;
--   2. the slack $\displaystyle r-\sum_{i\in S(\theta)}\Big(\frac{u_i}{\sigma_i}\Big)^2$;
--   3. the objective of (18), without its constant $\mathbf 1_S^\top\boldsymbol\mu$,
--   $$
--   \sum_{i\in S(\theta)}u_i+\sqrt{\Big[r-\sum_{i\in S(\theta)}\Big(\frac{u_i}{\sigma_i}\Big)^2\Big]\Big[\sum_{i\in S\setminus S(\theta)}\sigma_i^2\Big]}.
--   $$
--
--   Program (18) of Ghosal and Wiesemann optimizes this expression over $\theta\ge0$; it is the closed form of the quadratically constrained program (17) when the covariance bound is diagonal.
--
--   **Formalization Note** `capSet u σ S θ` is `S.filter (fun i => θ * u i < σ i ^ 2)`; `capSlack` and `diagObjective` are the slack and the objective. `Real.sqrt` returns $0$ on negative arguments; the theorem that uses the objective restricts $\theta$ to a nonnegative slack, so this default is never used.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §5.2, p. 727, Corollary 4, Eq. (18)

import Mathlib

namespace DRCVRP.Covariance

/-!
The one-dimensional program (18) of Corollary 4 in Ghosal and Wiesemann, *The Distributionally
Robust Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §5.2, p. 727, for a
diagonal covariance bound `Σ = diag(σ₁², …, σₙ²)`. Here `u : Fin n → ℝ` stands for the bound
`q^u` and `r` for `(1-ε)/ε`.
-/

/-- `S(θ) = {i ∈ S : σ_i² > θ · q^u_i}` (p. 727, below (18)). -/
noncomputable def capSet {n : ℕ} (u σ : Fin n → ℝ) (S : Finset (Fin n)) (θ : ℝ) : Finset (Fin n) :=
  S.filter (fun i => θ * u i < σ i ^ 2)

/-- The slack `(1-ε)/ε - ∑_{i ∈ S(θ)} (q^u_i/σ_i)²`, the first factor under the square root
of (18). -/
noncomputable def capSlack {n : ℕ} (u σ : Fin n → ℝ) (S : Finset (Fin n)) (r θ : ℝ) : ℝ :=
  r - ∑ i ∈ capSet u σ S θ, (u i / σ i) ^ 2

/-- The objective of (18) without the constant `1_Sᵀμ`:
`∑_{i ∈ S(θ)} q^u_i + √([(1-ε)/ε - ∑_{i ∈ S(θ)} (q^u_i/σ_i)²][∑_{i ∈ S∖S(θ)} σ_i²])`. -/
noncomputable def diagObjective {n : ℕ} (u σ : Fin n → ℝ) (S : Finset (Fin n)) (r θ : ℝ) : ℝ :=
  ∑ i ∈ capSet u σ S θ, u i +
    Real.sqrt (capSlack u σ S r θ * ∑ i ∈ S \ capSet u σ S θ, σ i ^ 2)

end DRCVRP.Covariance


