-- Prove2me | Definitions.Def_CvitanicKaratzas92_Existence_Dual
-- name    : CvitanicKaratzas92_Existence_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:06.027126+00:00
-- url     : https://prove2.me/theorems/6fc9e385-d34f-422f-aaa5-87dea2581973
-- title:
--   Sections 12–13 — dual value, minimizer condition, and extension to the energy space
-- statement:
--   For $y>0$ and an auxiliary drift $\nu\in\mathcal D$, the dual objective $\widetilde J(y;\nu)$ is the expected running and terminal conjugate utility evaluated at $yH_\nu$. Its value is the infimum over the precise class $\mathcal D$:
--
--   $$\widetilde V(y)=\inf_{\nu\in\mathcal D}\widetilde J(y;\nu).$$
--
--   The dual-attainment condition (12.9) asserts that, for every $y>0$, a minimizer $\lambda_y\in\mathcal D'$ exists. The extension (13.3) defines $\widetilde J_y$ on the finite-energy process space $\mathcal H$: it uses the explicit exponential formula for $\nu\in\mathcal G$, where $\nu$ lies in the effective domain of the support function almost everywhere, and is $+\infty$ outside $\mathcal G$.
--
--   These definitions separate the existence target from the assumptions used to prove it. An optimal policy is an admissible triple whose expected utility dominates every other triple with the same initial capital.
--
--   **Formalization Note** The extension retains infinite values of the support-function integral; on $\mathcal D$ it agrees with the earlier dual objective almost everywhere. Assumption 6.2 is included in the shared standing conditions. Condition (12.9) is a separate predicate and is never assumed in the goal theorem.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 791–792 and 794, (12.1)–(12.2), (12.9), (13.1)–(13.3); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Wealth

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

def Standing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : VProc d Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) : Prop :=
  P.IsComplete ∧ EthierKurtz.IsStandardBrownian P W ∧
  IsAugmentedBrownianFiltration P W 𝓕 ∧
  IsItoIntegralOperator P 𝓕 T W I ∧
  Market.Standing P 𝓕 T M ∧ ConstraintStanding K ∧
  UtilityStanding T U1 U2 ∧
  ∀ x : ℝ, 0 < x → V0 P 𝓕 T M I U1 U2 x < ⊤

def IsOptimal {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (x : ℝ) (p : Policy d Ω) : Prop :=
  A' P 𝓕 T M I K U1 U2 x p ∧
  ∀ q : Policy d Ω, A' P 𝓕 T M I K U1 U2 x q →
    J P T U1 U2 q ≤ J P T U1 U2 p

/-- (12.1), the dual objective for ν in 𝒟. -/
noncomputable def Jtilde {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (M : Market d Ω)
    (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (y : ℝ) (ν : VProc d Ω) : EReal :=
  expectExtended (spaceTime P T)
    (fun q => conjExt (U1 q.1.toNNReal) (y * HNu M I K ν q.1.toNNReal q.2)) +
  expectExtended P
    (fun ω => conjExt U2 (y * HNu M I K ν T ω))

/-- The infimum in (12.1) ranges over 𝒟 of (8.1). -/
noncomputable def Vtilde {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) (y : ℝ) : EReal :=
  ⨅ ν : {ν : VProc d Ω // IsD P 𝓕 T K ν},
    Jtilde P T M I K U1 U2 y ν.val

def Cond122 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → ∃ ν : VProc d Ω,
    IsD P 𝓕 T K ν ∧ Jtilde P T M I K U1 U2 y ν < ⊤

def Cond129 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → ∃ ν : VProc d Ω,
    IsD' P 𝓕 T M I K U1 U2 ν ∧
    Vtilde P 𝓕 T M I K U1 U2 y = Jtilde P T M I K U1 U2 y ν

def IsG {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (K : Set (Vec d)) (ν : VProc d Ω) : Prop :=
  IsH P 𝓕 T ν ∧
  ∀ᵐ q ∂(spaceTime P T), ν q.1.toNNReal q.2 ∈ barrierCone K

/-- The extended value of the time integral of the support function. -/
noncomputable def deltaIntegral {d : ℕ} {Ω : Type*} (K : Set (Vec d))
    (ν : VProc d Ω) (t : ℝ≥0) (ω : Ω) : EReal :=
  ((∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      epos (delta K (ν s.toNNReal ω)) ∂volume : ℝ≥0∞) : EReal) -
    ((∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      eneg (delta K (ν s.toNNReal ω)) ∂volume : ℝ≥0∞) : EReal)

/-- exp(-∞)=0 in the extension (13.3); finite values use the real exponential. -/
noncomputable def extendedDiscount {d : ℕ} {Ω : Type*}
    (M : Market d Ω) (K : Set (Vec d)) (ν : VProc d Ω)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if deltaIntegral K ν t ω = ⊤ then 0 else
    Real.exp (-(∫ s in Set.Icc (0 : ℝ) (t : ℝ), M.r s.toNNReal ω) -
      (deltaIntegral K ν t ω).toReal)

/-- Formula (13.3) on 𝒢, with +∞ outside 𝒢. -/
noncomputable def JyExt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (y : ℝ) (ν : VProc d Ω) : EReal := by
  classical
  exact if IsG P 𝓕 T K ν then
    expectExtended (spaceTime P T)
      (fun q => conjExt (U1 q.1.toNNReal)
        (y * extendedDiscount M K ν q.1.toNNReal q.2 *
          ZNu M I ν q.1.toNNReal q.2)) +
    expectExtended P
      (fun ω => conjExt U2
        (y * extendedDiscount M K ν T ω * ZNu M I ν T ω))
  else ⊤

/-- The Hilbert norm of a finite-energy process, using its L² norm squared. -/
noncomputable def hNorm {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (ν : VProc d Ω) : ℝ :=
  Real.sqrt ((∫⁻ q, ENNReal.ofReal (‖ν q.1.toNNReal q.2‖ ^ 2)
    ∂(spaceTime P T)).toReal)

/-- Convexity of an extended-real function, including its infinite values. -/
def EConvexOn (f : ℝ → EReal) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    f (s * a + (1 - s) * b) ≤
      (s : EReal) * f a + ((1 - s : ℝ) : EReal) * f b

end CvitanicKaratzas92.Existence


