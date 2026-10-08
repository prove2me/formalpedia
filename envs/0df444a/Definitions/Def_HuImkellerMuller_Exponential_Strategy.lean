-- Prove2me | Definitions.Def_HuImkellerMuller_Exponential_Strategy
-- name    : HuImkellerMuller_Exponential_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:53.153026+00:00
-- url     : https://prove2.me/theorems/04a8dd45-d24d-482a-bb0f-50df0b9ba309
-- title:
--   Remark 5, p. 6 and (5), p. 7 — wealth X^(p), the admissible set 𝒜 and the value function V(x)
-- statement:
--   This module defines the exponential-utility problem (5) of Hu, Imkeller and Müller (2005), in the formulation of Remark 5.
--
--   Let $I$ be an Itô-integral operator for the Brownian motion $W$, so that $I(p)_t=\int_0^t p_s\,dW_s$. A **strategy** is an $\mathbb R^{1\times m}$-valued process $p_t=\pi_t\sigma_t$ (the amounts invested, expressed in the noise coordinates). Its **wealth process** with initial capital $x$ is
--   $$X^{(p)}_t = x+\int_0^t p_u\,(dW_u+\theta_u\,du),\qquad t\in[0,T].$$
--
--   Fix the risk aversion $\alpha>0$ and the constraint set $\tilde C$. The set $\mathcal A$ of **admissible strategies** consists of the processes $p$ such that
--
--   1. $p$ is predictable;
--   2. $E\big[\int_0^T|p_t|^2\,dt\big]<\infty$;
--   3. $p_t(\omega)\in C_t(\omega)$ for $\lambda\otimes P$-a.e. $(t,\omega)$;
--   4. the family $\{\exp(-\alpha X^{(p)}_\tau) : \tau \text{ stopping time with values in } [0,T]\}$ is uniformly integrable.
--
--   For a liability $F$, the **expected utility** of $p$ is $E\big[-\exp(-\alpha(X^{(p)}_T-F))\big]\in[-\infty,0]$, and the **value function** is
--   $$V(x)=\sup_{p\in\mathcal A} E\Big[-\exp\Big(-\alpha\Big(x+\int_0^T p_t\,(dW_t+\theta_t\,dt)-F\Big)\Big)\Big].$$
--
--   The main theorem of the mission identifies $V(x)$ through a quadratic BSDE.
--
--   **Formalization Note** The expectation of the nonpositive variable $-\exp(\cdot)$ is taken as minus the lower integral of $\exp(\cdot)$ in $[0,\infty]$, so it lies in $[-\infty,0]$ as an extended real; a Bochner integral would return the junk value $0$ for non-integrable strategies and make every such strategy look optimal. $V(x)$ is an extended real (it would be $-\infty$ if $\mathcal A$ were empty). The constraint, written "$P$-a.s." in Remark 5, is read $\lambda\otimes P$-a.e., Definition 1's wording. Uniform integrability is Mathlib's `UniformIntegrable … 1 P` over the family indexed by stopping times $\tau\le T$; the stochastic integral is the operator `I` of the published module `CvitanicKaratzas92_Optimality_Market`. Only the $p$-formulation of Remark 5 is formalized, not the $\pi$-formulation of Definition 1 or their equivalence.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, wealth p. 4; Definition 1, p. 5; Remark 5, p. 6; problem (5), p. 7

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_Market

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}

/-- The wealth process of a strategy `p` (amounts `p_t = π_t σ_t ∈ ℝ^{1×m}`) with initial capital
`x` (p. 4 and Remark 5, p. 6): `X^{(p)}_t = x + ∫₀ᵗ p_u dW_u + ∫₀ᵗ p_u θ_u du`, the stochastic integral
being given by the Itô-integral operator `I`. -/
noncomputable def wealth (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ) (x : ℝ)
    (p : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + I p t ω + ∫ u in Set.Icc (0 : ℝ) t, inner ℝ (p u.toNNReal ω) (theta b σ u.toNNReal ω)

/-- Remark 5, p. 6: the set `𝒜` of admissible strategies. `p` is an `ℝ^{1×m}`-valued predictable
process with `E[∫₀ᵀ |p_t|² dt] < ∞`, `p_t(ω) ∈ C_t(ω)` for `λ ⊗ P`-a.e. `(t, ω)`, and the family
`{exp(−α X^{(p)}_τ) : τ stopping time with values in [0, T]}` is uniformly integrable. -/
def Admissible (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (Ct : Set (Fin d → ℝ)) (α x : ℝ) (p : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  IsPredictable 𝓕 p ∧
  (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ‖p s.toNNReal ω‖ₑ ^ 2) ∂P) < ⊤ ∧
  (∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
    p q.1.toNNReal q.2 ∈ Cset Ct σ q.1.toNNReal q.2) ∧
  UniformIntegrable
    (fun τ : {τ : Ω → WithTop ℝ≥0 // IsStoppingTime 𝓕 τ ∧ ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)} =>
      fun ω => Real.exp (-α * wealth I b σ x p ((τ.1 ω).untopD T) ω)) 1 P

/-- The expected utility `E[−exp(−α(X^{(p)}_T − F))]` of a strategy `p` with initial capital `x` and
liability `F`, as an extended real in `[−∞, 0]`: minus the lower integral of the nonnegative
random variable `exp(−α(X^{(p)}_T − F))`. -/
noncomputable def expectedUtility (P : Measure Ω) (T : ℝ≥0)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (α : ℝ) (F : Ω → ℝ) (x : ℝ) (p : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : EReal :=
  -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-α * (wealth I b σ x p T ω - F ω))) ∂P) : ℝ≥0∞) : EReal)

/-- (5), p. 7: the value function
`V(x) = sup_{p ∈ 𝒜} E[−exp(−α(x + ∫₀ᵀ p_t (dW_t + θ_t dt) − F))]`, an extended real. -/
noncomputable def V (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (Ct : Set (Fin d → ℝ)) (α : ℝ) (F : Ω → ℝ) (x : ℝ) : EReal :=
  ⨆ (p : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (_ : Admissible P 𝓕 T I b σ Ct α x p),
    expectedUtility P T I b σ α F x p

end HuImkellerMuller.Exponential


