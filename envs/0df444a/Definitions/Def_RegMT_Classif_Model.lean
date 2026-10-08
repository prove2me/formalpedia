-- Prove2me | Definitions.Def_RegMT_Classif_Model
-- name    : RegMT_Classif_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:30.547988+00:00
-- url     : https://prove2.me/theorems/fece0d08-36f6-4c0d-9a0d-2797525534e8
-- title:
--   §1.1, (4), (18) — classification loss and finite-program values
-- statement:
--   Let a training sample consist of $N$ feature-label pairs $(\hat x_i,\hat y_i)$, with $\hat y_i\in\{-1,+1\}$. A classifier $w$ assigns margin $y\langle w,x\rangle$ to $(x,y)$, and $L$ is a univariate loss. This file defines the following objects for Theorem 3.11(ii).
--
--   1. The **effective conjugate domain** is $\Theta=\{\theta:L^*(\theta)<\infty\}$, where $L^*(\theta)=\sup_z(\theta z-L(z))$. Its slope bound is $\sup_{\theta\in\Theta}|\theta|$.
--   2. The **worst-case classification loss** for fixed $w$ is
--   $$\sup_{Q\in\mathbb B_\rho(\hat P_N)}\mathbb E^Q[L(y\langle w,x\rangle)].$$
--   3. The **finite program at fixed $w$** minimizes $\lambda\rho+N^{-1}\sum_i s_i$ over $(\lambda,s)$ subject to $L(\hat y_i\langle w,\hat x_i\rangle)\le s_i$, $L(-\hat y_i\langle w,\hat x_i\rangle)-\kappa\lambda\le s_i$ for each $i$, and $\operatorname{lip}(L)\|w\|_*\le\lambda$. An intermediate version replaces $\operatorname{lip}(L)$ by $\sup_{\theta\in\Theta}|\theta|$.
--
--   The program is the finite-dimensional counterpart of the optimization over probability distributions in (4).
--
--   **Formalization Note** The shared published definitions supply the Wasserstein ball, the label-switching cost, the empirical distribution, and the Lipschitz modulus. Values lie in $[0,\infty]$. The finite-program objective is nonnegative whenever $\rho\ge0$ and $L\ge0$ on its feasible set.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp. 4, 7, 11, 30, 35, §1.1, (3), (4), (16), (18), proof of Lemma A.3 and Theorem 3.11

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open MeasureTheory
open scoped ENNReal

namespace RegMT.Classif

open DRLogReg.Reformulation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The effective domain of the conjugate `L*`: `L*(θ) = sup_z (θz - L(z))` is finite
exactly when the range in this definition is bounded above. -/
def conjDom (L : ℝ → ℝ) : Set ℝ :=
  {θ | BddAbove (Set.range fun z : ℝ => θ * z - L z)}

/-- `sup {|θ| : L*(θ) < ∞}`, the conjugate-domain expression on pp. 30 and 35. -/
noncomputable def conjSlope (L : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ θ ∈ conjDom L, ENNReal.ofReal |θ|

/-- The feasible pairs `(λ,s)` in program (18), at a fixed classifier `w`. The third
constraint uses the Lipschitz modulus, not an arbitrary Lipschitz constant. -/
def feasible18 {N : ℕ} (κ : ℝ) (xhat : Fin N → V) (yhat : Fin N → Bool)
    (L : ℝ → ℝ) (w : V →L[ℝ] ℝ) : Set (ℝ × (Fin N → ℝ)) :=
  {q | (∀ i, L (sgn (yhat i) * w (xhat i)) ≤ q.2 i) ∧
    (∀ i, L (-(sgn (yhat i) * w (xhat i))) - κ * q.1 ≤ q.2 i) ∧
    (WassersteinDRO.Duality.lipschitzModulus L).toReal * ‖w‖ ≤ q.1}

/-- The intermediate feasible set in the display after Lemma A.3, with the conjugate
domain slope bound in place of `lip(L)`. -/
def feasibleTheta {N : ℕ} (κ : ℝ) (xhat : Fin N → V) (yhat : Fin N → Bool)
    (L : ℝ → ℝ) (w : V →L[ℝ] ℝ) : Set (ℝ × (Fin N → ℝ)) :=
  {q | (∀ i, L (sgn (yhat i) * w (xhat i)) ≤ q.2 i) ∧
    (∀ i, L (-(sgn (yhat i) * w (xhat i))) - κ * q.1 ≤ q.2 i) ∧
    (conjSlope L).toReal * ‖w‖ ≤ q.1}

/-- The fixed-`w` value of program (18). For `ρ ≥ 0` and a nonnegative loss, every
feasible objective is nonnegative, so `ENNReal.ofReal` preserves its value. -/
noncomputable def value18 {N : ℕ} (κ ρ : ℝ) (xhat : Fin N → V)
    (yhat : Fin N → Bool) (L : ℝ → ℝ) (w : V →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨅ q ∈ feasible18 κ xhat yhat L w,
    ENNReal.ofReal (q.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2 i)

/-- The intermediate fixed-`w` program on p. 35 before replacing the conjugate-domain
slope bound by `lip(L)`. -/
noncomputable def valueTheta {N : ℕ} (κ ρ : ℝ) (xhat : Fin N → V)
    (yhat : Fin N → Bool) (L : ℝ → ℝ) (w : V →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨅ q ∈ feasibleTheta κ xhat yhat L w,
    ENNReal.ofReal (q.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2 i)

variable [MeasurableSpace V]

/-- The fixed-`w` worst-case loss in (4) with classification loss `L(y⟨w,x⟩)`, over
the Wasserstein ball defined by (3) and the label-switching transport cost (16). -/
noncomputable def worstCaseLoss {N : ℕ} (κ ρ : ℝ) (xhat : Fin N → V)
    (yhat : Fin N → Bool) (L : ℝ → ℝ) (w : V →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨆ Q ∈ wassersteinBall κ ρ (empirical xhat yhat),
    ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q

end RegMT.Classif


