-- Prove2me | Definitions.Def_WassFSG_Lip_Setting
-- name    : WassFSG_Lip_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:07.981082+00:00
-- url     : https://prove2.me/theorems/0cd4d3d2-5119-4809-a1a5-1a8f449a234c
-- title:
--   Sec. 2, Def. 1, Assumption 1 — W₁, P₁(Z), the Wasserstein regularizer R_{Q,1}, T₁(τ), ‖f‖_Lip, empirical mean and measure
-- statement:
--   Let $\mathcal Z$ be a separable real Banach space with norm $\|\cdot\|$ and its Borel $\sigma$-algebra. This file fixes the objects of order $p = 1$ used throughout the mission.
--
--   1. **First moments.** $\mathcal P_1(\mathcal Z)$ is the set of Borel probability measures $\mathbb Q$ with $\mathbb E_{\mathbb Q}\|z\| < \infty$.
--   2. **1-Wasserstein distance.** For measures $\mathbb P, \mathbb Q$,
--   $$
--   \mathcal W_1(\mathbb P,\mathbb Q) = \inf\Big\{ \mathbb E_{(\tilde z, z)\sim\pi}\|\tilde z - z\| \;:\; \pi \text{ a probability measure on } \mathcal Z^2 \text{ with marginals } \mathbb P, \mathbb Q \Big\} \in [0,\infty].
--   $$
--   3. **Wasserstein regularizer.** For $\mathbb Q$, a radius $\rho$ and a loss $f:\mathcal Z\to\mathbb R$,
--   $$
--   \mathcal R_{\mathbb Q,1}(\rho; f) = \sup\big\{ \mathbb E_{\mathbb P}[f] : \mathbb P\in\mathcal P_1(\mathcal Z),\ \mathcal W_1(\mathbb P,\mathbb Q)\le\rho \big\} - \mathbb E_{\mathbb Q}[f],
--   $$
--   the gap between the Wasserstein robust loss and the nominal loss, an extended real number.
--   4. **Transportation-information inequality $T_1(\tau)$.** A distribution $\mathbb P \in \mathcal P_1(\mathcal Z)$ satisfies $T_1(\tau)$, for a constant $\tau > 0$, if
--   $$
--   \mathcal W_1(\mathbb Q,\mathbb P) \le \sqrt{\tau\, H(\mathbb Q\,\|\,\mathbb P)} \qquad \text{for all } \mathbb Q\in\mathcal P_1(\mathcal Z),
--   $$
--   where $H(\mathbb Q\|\mathbb P) = \int \log(d\mathbb Q/d\mathbb P)\,d\mathbb Q$ is the relative entropy ($+\infty$ unless $\mathbb Q \ll \mathbb P$).
--   5. **Lipschitz norm.** $\|f\|_{\mathrm{Lip}} = \sup_{z\ne z'} |f(z') - f(z)|/\|z'-z\|$, the best Lipschitz constant of $f$ (the shared definition `WassFSG.Conc.lipNorm`, imported from `WassFSG.Conc.Setting`).
--   6. **Assumption 1(I).** A class $\mathcal F$ of losses satisfies it with constant $\gamma_1 > 0$ if $f(\tilde z) - f(z) \le \gamma_1\|\tilde z - z\|$ for every $f\in\mathcal F$ and all $z,\tilde z\in\mathcal Z$.
--   7. **Assumption 1(II).** $\operatorname{diam}(\mathcal Z) = \infty$, and every $f\in\mathcal F$ attains its Lipschitz norm at infinity: there is $z_0$ with
--   $$
--   \limsup_{\|z - z_0\|\to\infty} \frac{f(z) - f(z_0)}{\|z - z_0\|} = \|f\|_{\mathrm{Lip}}.
--   $$
--   8. **Empirical objects.** For a sample $z = (z_1,\dots,z_n)$, the empirical mean is $\mathbb E_{\mathbb P_n}[f] = \frac1n\sum_{i=1}^n f(z_i)$ and the empirical distribution is $\mathbb P_n = \frac1n\sum_{i=1}^n \delta_{z_i}$.
--
--   These are the paper's objects for the case $p = 1$; every statement of the mission is phrased in them.
--
--   **Formalization Note** The Wasserstein distance is used through its first power, $\mathcal W_1^1$, the published optimal-transport cost `RWPI.SqrtLasso.transportCost` with cost $\|u - w\|$, so "$\mathcal W_1(\mathbb P,\mathbb Q)\le\rho$" reads `W1 P Q ≤ ENNReal.ofReal ρ`. Expectations inside the regularizer are the extended integrals $\int f^+ - \int f^-$ of the published `ModelRiskOT.Duality.extIntegral`, so the supremum is meaningful even before integrability is known; for a Lipschitz $f$ and $\mathbb P \in \mathcal P_1$ it is the ordinary integral. $T_1(\tau)$ includes $\tau > 0$ and $\mathbb P\in\mathcal P_1(\mathcal Z)$, as Definition 1 does; the square root is the $\tfrac12$-power in $[0,\infty]$. The diameter condition of Assumption 1(II) is stated as "$\mathcal Z$ is not bounded" (Lean's `Metric.diam` is $0$ on unbounded sets), and the limit superior is taken in the extended reals along the filter $\|z - z_0\|\to\infty$. The Lipschitz norm is a real supremum; it is the true supremum whenever $f$ is Lipschitz, which every statement using it assumes. This module imports `WassFSG.Conc.Setting` for that Lipschitz norm only.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Sec. 2 Notation (p. 4), Wasserstein regularizer and Assumption 1 (p. 5), Definition 1 (p. 6)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Conc_Setting

open MeasureTheory

namespace WassFSG.Lip

variable {Z : Type*} [NormedAddCommGroup Z] [MeasurableSpace Z]

/-- The 1-Wasserstein distance `W₁(P, Q)` (Gao, Sec. 2, p. 4, with `p = 1`): the optimal transport
cost for the cost `‖z̃ - z‖`, an infimum over probability couplings `π` of `P` (first marginal) and
`Q` (second marginal) of `E_π ‖z̃ - z‖`, valued in `[0, ∞]`. -/
noncomputable def W1 (P Q : Measure Z) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun u w => ‖u - w‖ₑ) P Q

/-- `Q ∈ P₁(Z)` (Gao, Sec. 2, p. 4): `Q` is a (Borel) probability measure with finite first moment
`E_Q ‖z‖ < ∞`. -/
def IsP1 (Q : Measure Z) : Prop :=
  IsProbabilityMeasure Q ∧ ∫⁻ z, ‖z‖ₑ ∂Q < ⊤

/-- The Wasserstein regularizer `R_{Q,1}(ρ; f)` (Gao, Sec. 2, p. 5, with `p = 1`):
`sup { E_P[f] : P ∈ P₁(Z), W₁(P, Q) ≤ ρ } − E_Q[f]`, valued in `EReal`. Expectations are the
extended integrals `∫ f⁺ − ∫ f⁻` (`ModelRiskOT.Duality.extIntegral`). -/
noncomputable def regularizer (Q : Measure Z) (ρ : ℝ) (f : Z → ℝ) : EReal :=
  (⨆ (P : Measure Z) (_ : IsP1 P ∧ W1 P Q ≤ ENNReal.ofReal ρ),
      ModelRiskOT.Duality.extIntegral P (fun z => (f z : EReal)))
    - ModelRiskOT.Duality.extIntegral Q (fun z => (f z : EReal))

/-- The transportation-information inequality `T₁(τ)` (Gao, Definition 1, p. 6, with `p = 1`):
`τ > 0`, `P ∈ P₁(Z)`, and `W₁(Q, P) ≤ √(τ H(Q‖P))` for every `Q ∈ P₁(Z)`, where `H(Q‖P)` is the
relative entropy (Mathlib's `klDiv`, equal to `∞` unless `Q ≪ P` with integrable log-likelihood
ratio). -/
def IsT1 (τ : ℝ) (P : Measure Z) : Prop :=
  0 < τ ∧ IsP1 P ∧ ∀ Q : Measure Z, IsP1 Q →
    W1 Q P ≤ (ENNReal.ofReal τ * InformationTheory.klDiv Q P) ^ (1 / 2 : ℝ)

/-- Assumption 1(I) (Gao, p. 5): `γ₁ > 0` and `f(z̃) − f(z) ≤ γ₁ ‖z̃ − z‖` for every `f ∈ F` and
all `z, z̃ ∈ Z`. -/
def LipBound (γ₁ : ℝ) (F : Set (Z → ℝ)) : Prop :=
  0 < γ₁ ∧ ∀ f ∈ F, ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖

/-- Assumption 1(II) (Gao, p. 5): `diam(Z) = ∞` (the whole space is unbounded), and for every
`f ∈ F` there is `z₀ ∈ Z` with `limsup_{‖z − z₀‖ → ∞} (f(z) − f(z₀)) / ‖z − z₀‖ = ‖f‖_Lip`
(the limit superior is taken in `EReal`). -/
def LipAttainedAtInfinity (F : Set (Z → ℝ)) : Prop :=
  ¬ Bornology.IsBounded (Set.univ : Set Z) ∧ ∀ f ∈ F, ∃ z₀ : Z,
    Filter.limsup (fun z => (((f z - f z₀) / ‖z - z₀‖ : ℝ) : EReal))
      (Filter.comap (fun z => ‖z - z₀‖) Filter.atTop) = (WassFSG.Conc.lipNorm f : EReal)

/-- The empirical mean `E_{P_n}[f] = (1/n) ∑ᵢ f(zᵢ)` of `f` on the sample `z = (z₁, …, zₙ)`. -/
noncomputable def empMean {n : ℕ} (z : Fin n → Z) (f : Z → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f (z i)

/-- The empirical distribution `P_n = (1/n) ∑ᵢ δ_{zᵢ}` of the sample `z = (z₁, …, zₙ)`. -/
noncomputable def empMeasure {n : ℕ} (z : Fin n → Z) : Measure Z :=
  (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (z i)

end WassFSG.Lip


