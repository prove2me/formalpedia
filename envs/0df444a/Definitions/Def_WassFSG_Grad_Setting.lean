-- Prove2me | Definitions.Def_WassFSG_Grad_Setting
-- name    : WassFSG_Grad_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T11:27:21.917378+00:00
-- url     : https://prove2.me/theorems/4b4b500d-94bc-4935-a71d-c1310f81e5e7
-- title:
--   Sec. 2, Def. 1, Assumption 2 — W₂, P₂(Z), the regularizer R_{Q,2}, T₂(τ), gradient norms ‖‖∇f‖_*‖_{Q,2}, empirical mean and measure
-- statement:
--   Let $\mathcal Z$ be a separable real Banach space with norm $\|\cdot\|$, dual norm $\|\cdot\|_*$ and its Borel $\sigma$-algebra. This file fixes the objects of order $p = 2$ used throughout the mission.
--
--   1. **Second moments.** $\mathcal P_2(\mathcal Z)$ is the set of Borel probability measures $\mathbb Q$ with $\mathbb E_{\mathbb Q}\|z\|^2 < \infty$.
--   2. **2-Wasserstein distance.** For measures $\mathbb P, \mathbb Q$,
--   $$
--   \mathcal W_2(\mathbb P,\mathbb Q)^2 = \inf\Big\{ \mathbb E_{(\tilde z, z)\sim\pi}\|\tilde z - z\|^2 \;:\; \pi \text{ a probability measure on } \mathcal Z^2 \text{ with marginals } \mathbb P, \mathbb Q \Big\} \in [0,\infty].
--   $$
--   3. **Wasserstein regularizer.** For $\mathbb Q$, a radius $\rho\ge 0$ and a loss $f:\mathcal Z\to\mathbb R$,
--   $$
--   \mathcal R_{\mathbb Q,2}(\rho; f) = \sup\big\{ \mathbb E_{\mathbb P}[f] : \mathbb P\in\mathcal P_2(\mathcal Z),\ \mathcal W_2(\mathbb P,\mathbb Q)\le\rho \big\} - \mathbb E_{\mathbb Q}[f],
--   $$
--   the gap between the 2-Wasserstein robust loss and the nominal loss, an extended real number.
--   4. **Transportation-information inequality $T_2(\tau)$.** A distribution $\mathbb P \in \mathcal P_2(\mathcal Z)$ satisfies $T_2(\tau)$, for a constant $\tau > 0$, if
--   $$
--   \mathcal W_2(\mathbb Q,\mathbb P) \le \sqrt{\tau\, H(\mathbb Q\,\|\,\mathbb P)} \qquad \text{for all } \mathbb Q\in\mathcal P_2(\mathcal Z),
--   $$
--   where $H(\mathbb Q\|\mathbb P)$ is the relative entropy ($+\infty$ unless $\mathbb Q \ll \mathbb P$).
--   5. **Assumption 2 (smoothness).** A class $\mathcal F$ of losses satisfies it with constant $\hbar > 0$ if every $f\in\mathcal F$ is differentiable and
--   $$
--   \|\nabla f(\tilde z) - \nabla f(z)\|_* \le \hbar\,\|\tilde z - z\| \qquad \text{for all } z,\tilde z\in\mathcal Z.
--   $$
--   6. **Gradient norm.** For a measure $\mathbb Q$, $\|\|\nabla f\|_*\|_{\mathbb Q,2} = \big(\mathbb E_{z\sim\mathbb Q}\|\nabla f(z)\|_*^2\big)^{1/2}$.
--   7. **Empirical objects.** For a sample $z = (z_1,\dots,z_n)$: the empirical mean $\mathbb E_{\mathbb P_n}[f] = \frac1n\sum_{i=1}^n f(z_i)$, the empirical gradient norm $\|\|\nabla f\|_*\|_{\mathbb P_n,2} = \big(\frac1n\sum_{i=1}^n \|\nabla f(z_i)\|_*^2\big)^{1/2}$, and the empirical distribution $\mathbb P_n = \frac1n\sum_{i=1}^n \delta_{z_i}$.
--
--   These are the paper's objects for the case $p = 2$; every statement of the mission is phrased in them.
--
--   **Formalization Note** The Wasserstein distance enters through its square, the published optimal-transport cost `RWPI.SqrtLasso.transportCost` with cost $\|u-w\|^2$, so "$\mathcal W_2(\mathbb P,\mathbb Q)\le\rho$" reads `W2sq P Q ≤ ENNReal.ofReal (ρ ^ 2)` (every use has $\rho\ge0$), and $T_2(\tau)$ reads $\mathcal W_2(\mathbb Q,\mathbb P)^2\le\tau H(\mathbb Q\|\mathbb P)$ in $[0,\infty]$. Expectations inside the regularizer are the extended integrals $\int f^+ - \int f^-$ of the published `ModelRiskOT.Duality.extIntegral`. The gradient $\nabla f(z)$ is the Fréchet derivative `fderiv ℝ f z`, a continuous linear functional whose operator norm is the dual norm $\|\cdot\|_*$. The gradient norm uses the Bochner integral; under Assumption 2 and $\mathbb Q\in\mathcal P_2$ the integrand $\|\nabla f\|_*^2$ has quadratic growth and is integrable, so this is the true value.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Sec. 2 Notation (p. 4), Wasserstein regularizer and Assumption 2 (p. 5), Definition 1 (p. 6)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting

open MeasureTheory

namespace WassFSG.Grad

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]

/-- The squared 2-Wasserstein distance `W₂(P, Q)²` (Gao, Sec. 2, p. 4, with `p = 2`): the optimal
transport cost for the cost `‖z̃ - z‖²`, an infimum over probability couplings `π` of `P` (first
marginal) and `Q` (second marginal) of `E_π ‖z̃ - z‖²`, valued in `[0, ∞]`. -/
noncomputable def W2sq (P Q : Measure Z) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun u w => ‖u - w‖ₑ ^ 2) P Q

/-- `Q ∈ P₂(Z)` (Gao, Sec. 2, p. 4): `Q` is a (Borel) probability measure with finite second
moment `E_Q ‖z‖² < ∞`. -/
def IsP2 (Q : Measure Z) : Prop :=
  IsProbabilityMeasure Q ∧ ∫⁻ z, ‖z‖ₑ ^ 2 ∂Q < ⊤

/-- The Wasserstein regularizer `R_{Q,2}(ρ; f)` (Gao, Sec. 2, p. 5, with `p = 2`), for a radius
`ρ ≥ 0`: `sup { E_P[f] : P ∈ P₂(Z), W₂(P, Q) ≤ ρ } − E_Q[f]`, valued in `EReal`. The constraint
`W₂(P, Q) ≤ ρ` is written `W₂(P, Q)² ≤ ρ²`. Expectations are the extended integrals
`∫ f⁺ − ∫ f⁻` (`ModelRiskOT.Duality.extIntegral`). -/
noncomputable def regularizer (Q : Measure Z) (ρ : ℝ) (f : Z → ℝ) : EReal :=
  (⨆ (P : Measure Z) (_ : IsP2 P ∧ W2sq P Q ≤ ENNReal.ofReal (ρ ^ 2)),
      ModelRiskOT.Duality.extIntegral P (fun z => (f z : EReal)))
    - ModelRiskOT.Duality.extIntegral Q (fun z => (f z : EReal))

/-- The transportation-information inequality `T₂(τ)` (Gao, Definition 1, p. 6, with `p = 2`):
`τ > 0`, `P ∈ P₂(Z)`, and `W₂(Q, P) ≤ √(τ H(Q‖P))`, i.e. `W₂(Q, P)² ≤ τ H(Q‖P)`, for every
`Q ∈ P₂(Z)`, where `H(Q‖P)` is the relative entropy (Mathlib's `klDiv`, equal to `∞` unless
`Q ≪ P` with integrable log-likelihood ratio). -/
def IsT2 (τ : ℝ) (P : Measure Z) : Prop :=
  0 < τ ∧ IsP2 P ∧ ∀ Q : Measure Z, IsP2 Q →
    W2sq Q P ≤ ENNReal.ofReal τ * InformationTheory.klDiv Q P

/-- Assumption 2 (Gao, p. 5): `ħ > 0`, and every `f ∈ F` is (Fréchet) differentiable with
`‖∇f(z̃) − ∇f(z)‖_* ≤ ħ ‖z̃ − z‖` for all `z, z̃ ∈ Z`. The gradient `∇f(z)` is the derivative
`fderiv ℝ f z : Z →L[ℝ] ℝ`, whose operator norm is the dual norm `‖·‖_*`. -/
def GradLipBound (ħ : ℝ) (F : Set (Z → ℝ)) : Prop :=
  0 < ħ ∧ ∀ f ∈ F, Differentiable ℝ f ∧
    ∀ z z' : Z, ‖fderiv ℝ f z' - fderiv ℝ f z‖ ≤ ħ * ‖z' - z‖

/-- The `L²(Q)`-norm of the dual norm of the gradient,
`‖‖∇f‖_*‖_{Q,2} = (E_{z∼Q} ‖∇f(z)‖_*²)^{1/2}` (Gao, Notation, p. 4). -/
noncomputable def gradNorm (Q : Measure Z) (f : Z → ℝ) : ℝ :=
  Real.sqrt (∫ z, ‖fderiv ℝ f z‖ ^ 2 ∂Q)

/-- The empirical gradient norm `‖‖∇f‖_*‖_{P_n,2} = ((1/n) ∑ᵢ ‖∇f(zᵢ)‖_*²)^{1/2}` on the sample
`z = (z₁, …, zₙ)`. -/
noncomputable def empGradNorm {n : ℕ} (z : Fin n → Z) (f : Z → ℝ) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, ‖fderiv ℝ f (z i)‖ ^ 2)

end WassFSG.Grad


