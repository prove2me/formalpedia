-- Prove2me | Definitions.Def_LogMeanVar_Complete_Supplement_Countermodels
-- name    : LogMeanVar_Complete_Supplement_Countermodels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:59:42.880231+00:00
-- url     : https://prove2.me/theorems/6890cf0d-7115-4322-b835-ccce1cb498a4
-- title:
--   Theorems 3–4 (countermodels) — fast-growing rates and a Brownian-triggered state
-- statement:
--   Two concrete scalar models test the printed assumptions.
--
--   1. Take $T=\sigma=\gamma=1$, $\rho=0$, $X=B^X$ and $\mu(t,x)=r(t,x)=e^{x^4}$. Then $\theta=0$, policy (14) is zero, and its log return is $R_t=\int_0^te^{(B^X_s)^4}\,ds$. The exponential hypothesis uses the cancelled expression $\exp[-\rho^2R_1/4]$, equal to one at $\rho=0$.
--   2. Let $\tau$ be the first hit of level one by $B^X$. Take $T=2$, $\sigma=\gamma=1$, $\mu=r=x$, $m=2\sqrt{x}$, $\nu=0$ and the deterministic closed convex constraint $\Pi=\{0\}$. Set
--
--   $$X_t=(t-\tau)_+^2,\qquad U=\int_0^2X_s\,ds,\qquad Y_t=\mathbb E_t[U]-\int_0^tX_s\,ds.$$
--
--   These are explicit objects, not variables constrained by the desired conclusions. They expose respectively the missing finite-reward hypothesis in Theorem 3 and the unjustified Markov inference in Theorem 4.
--
--   **Formalization Note** The hitting time is an extended nonnegative infimum with empty-set value $+\infty$. The elapsed positive part is zero on the no-hit event. The real square root in $m$ is only evaluated at the nonnegative state on the counterexample. All coefficient functions are continuous in time.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 8, 18–19, O–11–O–13, (5), Theorems 3–4

import Definitions.Def_LogMeanVar_Complete_Supplement_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-! Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), p.8 (5), pp.18–19 Theorem 3,
pp.O–11–O–13 Theorem 4. Explicit countermodels to the printed hypotheses.
Formalization Note: these constructed test instances are not definitions printed
in the paper; DISPROOF.md records their mathematical role and the source gaps. -/
namespace LogMeanVar.Complete.Supplement

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Countermodel to the printed integrability assumptions of Theorem 3, p.18:
T=1, γ=1, ρ=0, μ=r=exp(x⁴), σ=1, dX=dB^X. All coefficient functions are continuous.
The positive rate has finite time integrals on each continuous path. -/
noncomputable def growthModel : Model where
  T := 1
  r := fun _ x => Real.exp (x ^ 4)
  μ := fun _ x => Real.exp (x ^ 4)
  σ := fun _ _ => 1
  m := fun _ _ => 0
  ν := fun _ _ => 1

noncomputable def growthState (W : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun s ω => W s.toNNReal ω

noncomputable def growthReturn (W : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => ∫ s in (0 : ℝ)..t, Real.exp (W s.toNNReal ω ^ 4)

/-- The cancelled exponent in Theorem 3's assumption at γ=1, θ=0.
It agrees with the printed expression for ρ≠0 and is 0 for ρ=0,
as supported by the p.19 zero-hedging discussion. -/
noncomputable def growthExponential (W : ℝ≥0 → Ω → ℝ) (ρ : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(1 / (4 : ℝ)) * (ρ ^ 2 * growthReturn W 1 ω))

/-- First hit of level 1. Infimum in ℝ≥0∞, hence an empty hitting set has value +∞,
not zero. This retains the no-hit event on the finite investment horizon. -/
noncomputable def firstHit (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  sInf {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) = u ∧ W t ω = 1}

/-- An adapted non-Markov solution of dX=2√X dt, X₀=0:
it waits until the Brownian hitting time τ and then equals (t-τ)².
The positive-part elapsed time is zero when τ=+∞. -/
noncomputable def waitingState (W : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => (ENNReal.ofReal t - firstHit W ω).toReal ^ 2

/-- Scalar countermodel within the full N,K≥1 domain of Theorem 4:
N=K=1, T=2, γ=1, μ=r=x, σ=1, m=2√x, ν=0, Π={0}, θ=0.
Then vhat=0 and the actual constrained driver (45) is g(t,z)=X_t. -/
noncomputable def waitingModel : Model where
  T := 2
  r := fun _ x => x
  μ := fun _ x => x
  σ := fun _ _ => 1
  m := fun _ x => 2 * Real.sqrt x
  ν := fun _ _ => 0

/-- Source Appendix C.3, p.O–11: explicit scalar constraint, selector,
objective and drift. These connect the waiting BSDE to the actual constrained
minimization in (45), rather than merely naming an unrelated driver. -/
def waitingConstraints (_t _x : ℝ) : Set ℝ := {0}

def waitingPortfolio (_t _z : ℝ) : ℝ := 0

noncomputable def scalarTheta (M : Model) (t x : ℝ) : ℝ :=
  (M.μ t x - M.r t x) / M.σ t x

noncomputable def allocationObjective (M : Model) (γ ρ t x z p : ℝ) : ℝ :=
  (M.σ t x * p - scalarTheta M t x) ^ 2 +
    γ * (M.σ t x * p + ρ * z) ^ 2

noncomputable def allocationDrift (M : Model) (t x p : ℝ) : ℝ :=
  M.r t x + scalarTheta M t x ^ 2 / 2 -
    (M.σ t x * p - scalarTheta M t x) ^ 2 / 2

noncomputable def waitingDriver (W : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ → ℝ :=
  fun t ω _ => waitingState W t ω

noncomputable def waitingReturn (W : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => ∫ s in (0 : ℝ)..t, waitingState W s ω

noncomputable def waitingPayoff (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..2, waitingState W s ω

/-- Canonical conditional value; a classical solution is allowed a continuous
modification of this version. No representing deterministic f is built in. -/
noncomputable def waitingValue (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (P[waitingPayoff W | F t.toNNReal]) ω -
    ∫ s in (0 : ℝ)..t, waitingState W s ω

end LogMeanVar.Complete.Supplement


