-- Prove2me | Definitions.Def_OptStopC1_SpaceDeriv_StoppingProblem
-- name    : OptStopC1_SpaceDeriv_StoppingProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:12.292291+00:00
-- url     : https://prove2.me/theorems/21affb1a-2e6a-4b97-9625-535e2d14b7d7
-- title:
--   Infinite-horizon optimal stopping problem and well-posed value function
-- statement:
--   Let $X^x$ be a standard Markov flow, let $\lambda\ge0$ be continuous, and let $G,H$ be continuous real functions. Define $\Lambda^x_t=\int_0^t\lambda(X^x_s)\,ds$. For a finite stopping time $\tau$ of the common filtration, its expected reward is
--
--   $$J(x,\tau)=E\!\left[e^{-\Lambda^x_\tau}G(X^x_\tau)+\int_0^\tau e^{-\Lambda^x_t}H(X^x_t)\,dt\right],\qquad V(x)=\sup_\tau J(x,\tau).$$
--
--   The **stopping set** is $D=\{x:V(x)=G(x)\}$, the **continuation set** is $C=\{x:V(x)>G(x)\}$, and the boundary used in the theorem is $D\cap\overline C$. **Well-posedness** requires integrable rewards for every admissible stopping time, an almost surely finite first entry time $\tau_D^x$ that is a stopping time, and optimality of $\tau_D^x$ against every admissible time, including equality of its payoff with $V(x)$.
--
--   This definition fixes the value function from the data; no theorem may choose $V$ independently. The generator condition (2.14) identifies the right derivative of the discounted transition semigroup on its smooth domain with the paper's diffusion, drift, killing, and jump expression. Its matrix is symmetric and positive semidefinite, and the jump kernel is a nonnegative measure off zero.
--
--   **Formalization Note** Time integrals use Lebesgue integration over real intervals and the nonnegative-time flow. On the null set where $\tau_D^x=+\infty$, the optimal payoff uses a finite modification.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 3–4, equations (2.1)–(2.5) and well-posedness paragraph; p. 7, equation (2.14)

import Definitions.Def_OptStopC1_SpaceDeriv_MarkovFlow

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} {𝔽 : Filtration ℝ≥0 mΩ}

/-- Infinite-horizon data for (2.1)-(2.3), on a shared Markov flow. -/
structure StoppingProblem (d : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ) where
  X : Flow d Ω
  rate : State d → ℝ
  G : State d → ℝ
  H : State d → ℝ
  standard : IsStandardMarkovFlow X P 𝔽
  rate_continuous : Continuous rate
  G_continuous : Continuous G
  H_continuous : Continuous H
  rate_nonnegative : ∀ x, 0 ≤ rate x

/-- Discount exponent along the flow, (2.3). -/
noncomputable def discount (p : StoppingProblem d Ω P 𝔽)
    (x : State d) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), p.rate (p.X x s.toNNReal ω)

/-- Admissible finite-valued stopping times for the common filtration. -/
def Admissible (𝔽 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime 𝔽 (fun ω => (τ ω : ℝ≥0∞))

/-- Pathwise discounted stopping reward plus running reward, (2.1). -/
noncomputable def payoffRandom (p : StoppingProblem d Ω P 𝔽)
    (x : State d) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(discount p x (τ ω) ω)) * p.G (p.X x (τ ω) ω) +
    ∫ t in (0 : ℝ)..(τ ω : ℝ),
      Real.exp (-(discount p x t.toNNReal ω)) * p.H (p.X x t.toNNReal ω)

/-- Expected payoff at a finite-valued stopping time. -/
noncomputable def payoff (p : StoppingProblem d Ω P 𝔽)
    (x : State d) (τ : Ω → ℝ≥0) : ℝ :=
  ∫ ω, payoffRandom p x τ ω ∂P

/-- Value function as the supremum over all common-filtration stopping times, (2.1). -/
noncomputable def value (p : StoppingProblem d Ω P 𝔽) (x : State d) : ℝ :=
  sSup {v : ℝ | ∃ τ : Ω → ℝ≥0, Admissible 𝔽 τ ∧ v = payoff p x τ}

/-- The stopping set, where the value equals the stopping reward. -/
noncomputable def stoppingSet (p : StoppingProblem d Ω P 𝔽) : Set (State d) :=
  {x | value p x = p.G x}

/-- The continuation set, where delaying is worth strictly more. -/
noncomputable def continuationSet (p : StoppingProblem d Ω P 𝔽) : Set (State d) :=
  {x | p.G x < value p x}

/-- The boundary points of the stopping set accumulated by continuation points. -/
noncomputable def stoppingBoundary (p : StoppingProblem d Ω P 𝔽) : Set (State d) :=
  stoppingSet p ∩ closure (continuationSet p)

/-- Explicit well-posedness: all admissible payoffs are integrable and the first
entry time of the stopping set attains their supremum. The finite modification
on the null set where the entry time is infinite is used only in the payoff. -/
noncomputable def WellPosed (p : StoppingProblem d Ω P 𝔽) : Prop :=
  (∀ x τ, Admissible 𝔽 τ → Integrable (payoffRandom p x τ) P) ∧
  (∀ x, IsStoppingTime 𝔽 (entryTime p.X x (stoppingSet p))) ∧
  (∀ x, ∀ᵐ ω ∂P, entryTime p.X x (stoppingSet p) ω ≠ ⊤) ∧
  (∀ x, Integrable (payoffRandom p x
    (finiteEntryTime p.X x (stoppingSet p))) P) ∧
  (∀ x τ, Admissible 𝔽 τ → payoff p x τ ≤
    payoff p x (finiteEntryTime p.X x (stoppingSet p))) ∧
  (∀ x, value p x = payoff p x
    (finiteEntryTime p.X x (stoppingSet p)))

/-- The discounted infinitesimal-generator representation (2.14), on its
smooth domain. The generator is the right derivative of the discounted
transition semigroup, so the displayed equality identifies its value rather
than choosing an unrelated operator. The page's "ν(x, dy) on ℝ^d ∖ {0}" excludes
zero jumps; since the integrand is in the post-jump position `y`, this is
`ν x {x} = 0` (the integrand vanishes there anyway). -/
noncomputable def HasGeneratorForm (p : StoppingProblem d Ω P 𝔽) : Prop :=
  ∃ (σ : State d → Fin d → Fin d → ℝ) (μ : State d → State d)
    (ν : State d → Measure (State d)),
    (∀ x i j, σ x i j = σ x j i) ∧
    (∀ x (v : State d), 0 ≤ ∑ i : Fin d, ∑ j : Fin d,
      σ x i j * v i * v j) ∧
    (∀ x, ν x {x} = 0) ∧
    ∀ (F : State d → ℝ) (x : State d) (l : ℝ),
      ContDiff ℝ 2 F →
      (∀ t : ℝ≥0, Integrable (fun ω =>
        Real.exp (-(discount p x t ω)) * F (p.X x t ω)) P) →
      Integrable (fun y : State d =>
        F y - F x - ∑ i : Fin d,
          (y i - x i) * (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ)))
        (ν x) →
      Tendsto (fun t : ℝ≥0 =>
        ((∫ ω, Real.exp (-(discount p x t ω)) * F (p.X x t ω) ∂P) - F x) /
          (t : ℝ)) (𝓝[Set.Ioi 0] 0) (𝓝 l) →
      l = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
        σ x i j *
          (fderiv ℝ (fun y : State d =>
            (fderiv ℝ F y) (EuclideanSpace.single i (1 : ℝ))) x)
            (EuclideanSpace.single j (1 : ℝ))) +
        (∑ i : Fin d, μ x i *
          (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ))) -
        p.rate x * F x +
        ∫ y, (F y - F x - ∑ i : Fin d,
          (y i - x i) * (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ))) ∂ν x

end OptStopC1.SpaceDeriv


