-- Prove2me | Definitions.Def_OAIQ4Sk000
-- name    : OAIQ4Sk000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T07:45:34.501859+00:00
-- url     : https://prove2.me/theorems/52d296e8-a4fd-447c-9523-da00e23134ae
-- title:
--   Definitions bundle OAIQ4Sk000 of the split of OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 406 declarations of OpenAI's Lean: 239 definitions, 21 inductive types or structures, 16 instances and 130 theorems. The definitions and types are `OAI.SKValue.BackwardBurgers`, `OAI.SKValue.BackwardBurgers.k`, `OAI.SKValue.BackwardBurgers.kt`, `OAI.SKValue.BackwardBurgers.kx`, `OAI.SKValue.BackwardBurgers.kxx`, `OAI.SKValue.BackwardBurgers.n`, `OAI.SKValue.BackwardBurgers.nt`, `OAI.SKValue.BackwardBurgers.nx`, `OAI.SKValue.BackwardBurgers.nxx`, `OAI.SKValue.BackwardBurgers.ratioJ`, `OAI.SKValue.BackwardBurgers.ratioJt`, `OAI.SKValue.BackwardBurgers.ratioJx`, `OAI.SKValue.BackwardBurgers.ratioJxx`, `OAI.SKValue.BackwardShape`, `OAI.SKValue.BackwardTest`, `OAI.SKValue.BoundedJoint`, `OAI.SKValue.BoundedSmooth`, `OAI.SKValue.BoundedSmoothFamily`, `OAI.SKValue.BoundedUniformLimit`, `OAI.SKValue.BrownianSpace.realFiltration`, `OAI.SKValue.Certificate.F₂`, `OAI.SKValue.Certificate.Q`, `OAI.SKValue.Certificate.T`, `OAI.SKValue.Certificate.W₂`, `OAI.SKValue.Certificate.remainder`, `OAI.SKValue.DependsBefore`, `OAI.SKValue.ExpGrowth`, `OAI.SKValue.ForcedTest`, `OAI.SKValue.ForwardBurgers`, `OAI.SKValue.ForwardDensityData`, `OAI.SKValue.ForwardDensityData.evolve`, `OAI.SKValue.ForwardDensityData.gaussian`, `OAI.SKValue.ForwardDensityData.jet`, `OAI.SKValue.ForwardDensityData.jump`, `OAI.SKValue.ForwardDensityData.weight`, `OAI.SKValue.ForwardShape`, `OAI.SKValue.GradientStrip`, `OAI.SKValue.GradientStripCore`, `OAI.SKValue.HeatProfile`, `OAI.SKValue.JetExpr` and 220 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKValue, in whole or in part: `SKValue_Coercivity_Coercivity`, `SKValue_Control_ControlIntegral`, `SKValue_Control_ControlStability`, `SKValue_Control_Controls`, `SKValue_Control_PolynomialGenerator`, `SKValue_Control_Regularity`, `SKValue_Control_StripRegularity`, `SKValue_Control_SupStability`, `SKValue_Equations_BackwardPolynomials`, `SKValue_Equations_BetaBound`, `SKValue_Equations_BrownianIncrementIndepPast`, `SKValue_Equations_CoupledComparison`, `SKValue_Equations_CoupledDensity`, `SKValue_Equations_CubicEnvelopeMean`, `SKValue_Equations_Cutoff`, `SKValue_Equations_DuhamelJets`, `SKValue_Equations_FiniteRounded`, `SKValue_Equations_ForcedGenerator`, `SKValue_Equations_ForwardComparison`, `SKValue_Equations_ForwardDensity`, `SKValue_Equations_GradientErrorConstant`, `SKValue_Equations_GradientStrip`, `SKValue_Equations_GradientStripCore`, `SKValue_Equations_InitialMax`, `SKValue_Equations_JetAlgebra`, `SKValue_Equations_PolynomialMoment`, `SKValue_Equations_PolynomialObservable`, `SKValue_Equations_ProfileShape`, `SKValue_Equations_RawIncrement`, `SKValue_Equations_RealFiltration`, `SKValue_Equations_ResponseJets`, `SKValue_Equations_ShiftedPairing`, `SKValue_Equations_ShortStripClose`, `SKValue_Equations_StrictProfile`, `SKValue_Equations_TestGenerator`, `SKValue_Equations_TestPatch`, `SKValue_Equations_TruncatedStieltjes`, `SKValue_Equations_UniformPolynomial`, `SKValue_Equations_ValueStrip`, `SKValue_Equations_WeightedCap`, `SKValue_Evolution_BoundedSmooth`, `SKValue_Evolution_BurgersJets`, `SKValue_Evolution_ColeHopf`, `SKValue_Evolution_ColeHopfPDE`, `SKValue_Evolution_FiniteStepEvolution`, `SKValue_Evolution_GridConvergence`, `SKValue_Evolution_GridProfile`, `SKValue_Evolution_HeatBounds`, `SKValue_Evolution_HeatContinuity`, `SKValue_Evolution_HeatConvexity`, `SKValue_Evolution_HeatDuality`, `SKValue_Evolution_HeatRegularity`, `SKValue_Evolution_HeatTransform`, `SKValue_Evolution_HigherPDE`, `SKValue_Evolution_LogCoshTerminal`, `SKValue_Evolution_LogHeatJets`, `SKValue_Evolution_SmoothEvolution`, `SKValue_Evolution_SmoothFamily`, `SKValue_Evolution_TerminalAlgebra`, `SKValue_Evolution_TerminalError`, `SKValue_Evolution_TestEvolution`, `SKValue_Evolution_TimePatch`, `SKValue_Gaussian_BrownianCoordinates`, `SKValue_Gaussian_CoupledCoordinates`, `SKValue_Gaussian_DensityJump`, `SKValue_Gaussian_EvenEvolution`, `SKValue_Gaussian_GaussianSquareVariance`, `SKValue_Gaussian_ProfileSplit`, `SKValue_Gaussian_ShiftedBrownianCoordinates`, `SKValue_Gaussian_SplitConvergence`, `SKValue_Gaussian_SplitShape`, `SKValue_Gaussian_UniformError`, `SKValue_GroundState_AdaptiveColumns`, `SKValue_GroundState_AffineComparison`, `SKValue_GroundState_BlockCoeff`, `SKValue_GroundState_BranchLaw`, `SKValue_GroundState_BranchMeanUpper`, `SKValue_GroundState_CascadeMoments`, `SKValue_GroundState_CascadePassage`, `SKValue_GroundState_EmpiricalLog`, `SKValue_GroundState_EmpiricalPower`, `SKValue_GroundState_EmpiricalVectors`, `SKValue_GroundState_ExponentialMoments`, `SKValue_GroundState_FieldTreeLaw`, `SKValue_GroundState_GaussianColumn`, `SKValue_GroundState_GaussianTranspose`, `SKValue_GroundState_GaussianTree`, `SKValue_GroundState_GramSchmidtLimit`, `SKValue_GroundState_GumbelMax`, `SKValue_GroundState_GumbelReplacement`, `SKValue_GroundState_LiteralLower`, `SKValue_GroundState_PredictableNormalizer`, `SKValue_GroundState_QuadraticSK`, `SKValue_GroundState_RandomColumn`, `SKValue_GroundState_RandomGuerra`, `SKValue_GroundState_RotatedCoefficients`, `SKValue_GroundState_RoundingSpin`, `SKValue_GroundState_StandardGaussian`, `SKValue_GroundState_TreeGuerra`, `SKValue_GroundState_TreeProductLaw`, `SKValue_GroundState_TreeWidths`, `SKValue_Processes_CrossMesh`, `SKValue_Processes_CrossMeshComparison`, `SKValue_Processes_DiffusionExistence`, `SKValue_Processes_EulerLimitProcess`, `SKValue_Processes_Feedback`, `SKValue_Processes_MeshBrownian`, `SKValue_Processes_MeshMaxError`, `SKValue_Processes_MeshRaw`, `SKValue_Processes_UnitMomentMartingale`, `SKValue_Processes_Volterra`, `SKValue_Variation_ContactVariations`, `SKValue_Variation_OrderVariations`, `SKValue_Variation_WeightedMoments`.
--
--   **Imports.** It imports the published bundle `Def_SKValue`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKValueG.weak_profile_guerra_upper`, `OAI.SKValue.IsDiffusion.contactPotential_continuous`, `OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvatureExpr_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvature_integral_terminal`, `OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip`, `OAI.SKValue.IsDiffusion.gradientMoment_continuous`, `OAI.SKValue.IsDiffusion.momentExpr_hasDerivAt`, `OAI.SKValue.IsDiffusion.moment_convexOn_zero_closed`, `OAI.SKValue.IsDiffusion.moment_difference_integrable`, `OAI.SKValue.IsDiffusion.parisi_first_value`, `OAI.SKValue.IsDiffusion.parisi_value_assembly`, `OAI.SKValue.IsDiffusion.splitResponse_tendsto`, `OAI.SKValue.IsMinimizer.coeff_constant_of_contactPositive`, `OAI.SKValue.IsMinimizer.contactPotential_nonneg`, `OAI.SKValue.IsMinimizer.contact_origin_of_positive`, `OAI.SKValue.IsMinimizer.moment_eq_at_contact`, `OAI.SKValue.SmoothTerminal.liftProfile_bound`, `OAI.SKValue.SmoothTerminal.profile_weak_error`, `OAI.SKValue.phi_evolution`, `OAI.SKValue.smoothApprox_tendsto`, `OAI.SKValue.sourceStripRegularity`, `OAI.SKValue.splitSmooth_tendsto`, `OAI.SKValue.split_profile_coercivity` and `OAI.SKValue.split_spatialJet_limit`; the proofs of `OAI.SKValueG.weak_profile_guerra_upper`, `OAI.SKValue.IsDiffusion.contactPotential_continuous`, `OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvatureExpr_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvature_integral_terminal`, `OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip`, `OAI.SKValue.IsDiffusion.gradientMoment_continuous`, `OAI.SKValue.IsDiffusion.momentExpr_hasDerivAt`, `OAI.SKValue.IsDiffusion.moment_convexOn_zero_closed`, `OAI.SKValue.IsDiffusion.moment_difference_integrable`, `OAI.SKValue.IsDiffusion.parisi_first_value`, `OAI.SKValue.IsDiffusion.parisi_value_assembly`, `OAI.SKValue.IsDiffusion.splitResponse_tendsto`, `OAI.SKValue.IsMinimizer.coeff_constant_of_contactPositive`, `OAI.SKValue.IsMinimizer.contactPotential_nonneg`, `OAI.SKValue.IsMinimizer.contact_origin_of_positive`, `OAI.SKValue.IsMinimizer.gradient_moment_contact`, `OAI.SKValue.IsMinimizer.moment_eq_at_contact`, `OAI.SKValue.SmoothTerminal.liftProfile_bound`, `OAI.SKValue.SmoothTerminal.profile_weak_error`, `OAI.SKValue.phi_evolution`, `OAI.SKValue.phi_gradient_difference_bound`, `OAI.SKValue.shiftedCoefficientSum_le_groundState`, `OAI.SKValue.smoothApprox_tendsto`, `OAI.SKValue.sourceStripRegularity`, `OAI.SKValue.splitSmooth_tendsto`, `OAI.SKValue.split_profile_coercivity`, `OAI.SKValue.split_spatialJet_limit` and `OAI.SKValue.value_consequences`.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKValue at commit adc7f12

import Mathlib
import Definitions.Def_SKValue

section
-- module Solutions.OAIQ4_Sk.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_JetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

inductive JetExpr where
  | const : ℝ → JetExpr
  | coord : ℕ → JetExpr
  | add : JetExpr → JetExpr → JetExpr
  | mul : JetExpr → JetExpr → JetExpr

namespace JetExpr
noncomputable def eval (R : ℕ → ℝ) : JetExpr → ℝ
  | const c => c
  | coord j => R j
  | add e f => eval R e+eval R f
  | mul e f => eval R e*eval R f

noncomputable def D (σ : ℕ → JetExpr) : JetExpr → JetExpr
  | const _ => const 0
  | coord j => σ j
  | add e f => add (D σ e) (D σ f)
  | mul e f => add (mul (D σ e) f) (mul e (D σ f))

lemma hasDerivAt_eval {R : ℕ → ℝ → ℝ} {σ : ℕ → JetExpr} {x : ℝ}
    (hR : ∀ j, HasDerivAt (R j) (eval (fun i ↦ R i x) (σ j)) x) (e : JetExpr) :
    HasDerivAt (fun y ↦ eval (fun i ↦ R i y) e) (eval (fun i ↦ R i x) (D σ e)) x := by
  induction e with
  | const c => exact hasDerivAt_const x c
  | coord j => exact hR j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

lemma continuous_eval {α : Type*} [TopologicalSpace α] {R : ℕ → α → ℝ}
    (hR : ∀ j, Continuous (R j)) (e : JetExpr) :
    Continuous (fun a ↦ eval (fun j ↦ R j a) e) := by
  induction e with
  | const c => exact continuous_const
  | coord j => exact hR j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

noncomputable def σx (j : ℕ) : JetExpr :=
  add (coord (j+1)) (mul (const (-1)) (mul (coord j) (coord 1)))

noncomputable def σh (j : ℕ) : JetExpr :=
  mul (const (1/2)) (add (coord (j+2)) (mul (const (-1)) (mul (coord j) (coord 2))))

noncomputable def logGradientJet : ℕ → JetExpr
  | 0 => coord 1
  | n+1 => D σx (logGradientJet n)

lemma eval_σx (R : ℕ → ℝ) (j : ℕ) : eval R (σx j)=R (j+1)-R j*R 1 := by
  simp only [σx,eval]; ring
lemma eval_σh (R : ℕ → ℝ) (j : ℕ) : eval R (σh j)=(1/2 : ℝ)*(R (j+2)-R j*R 2) := by
  simp only [σh,eval]; ring

lemma iteratedDeriv_logGradientJet {R : ℕ → ℝ → ℝ}
    (hs : ∀ j, ContDiff ℝ ∞ (R j))
    (hd : ∀ j, deriv (R j)=fun x ↦ R (j+1) x-R j x*R 1 x) (n : ℕ) :
    iteratedDeriv n (R 1)=fun x ↦ eval (fun j ↦ R j x) (logGradientJet n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    apply HasDerivAt.deriv
    apply hasDerivAt_eval
    intro j
    have hj := (((hs j).differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))) x).hasDerivAt
    simpa only [hd,eval_σx] using hj

end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_InitialMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

noncomputable def initialMax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n+1 => max (initialMax f n) (f (n+1))

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshMaxError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

noncomputable def meshMaxError {Ω : Type*} (T : ℝ) (X : ℝ → Ω → ℝ)
    (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  initialMax (fun j ↦ |Y N j ω-X ((j : ℝ)*(T/N)) ω|) N

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_PredictableNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def predictableNormalizer (H : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  (Real.sqrt (∫ ω, (H ω)^2 ∂μ))⁻¹

noncomputable def normalizedIncrement (H Z : Ω → ℝ) (μ : Measure Ω) : Ω → ℝ :=
  fun ω ↦ predictableNormalizer H μ * H ω * Z ω

def DependsBefore {N : ℕ} {β : Type*} (j : ℕ) (F : (Fin (N+1) → ℝ) → β) : Prop :=
  ∀ z z', (∀ i : Fin (N+1), (i : ℕ)<j → z i=z' i) → F z=F z'

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_GaussianSquareVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def gaussianSquareVariance : ℝ :=
  ∫ z : ℝ, (z^2-1)^2 ∂gaussianReal 0 1

noncomputable def cubicEnvelope (G K C : ℝ) (z : ℝ) : ℝ :=
  K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2)

noncomputable def cubicEnvelopeMoment (G K C : ℝ) : ℝ :=
  ∫ z : ℝ, (cubicEnvelope G K C z)^2 ∂gaussianReal 0 1

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

structure GradientStrip (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (K L : ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0 : ℝ) T)
  smooth : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 3 (u t)
  bounded : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x|≤1
  second_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (deriv (u t)) x|≤K
  third_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |iteratedDeriv 3 (u t) x|≤K
  product_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x*deriv (u t) x|≤K
  second_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |deriv (deriv (u s)) y-deriv (deriv (u t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |u s y*deriv (u s) y-u t x*deriv (u t) x|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ x, IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume 0 T
  product_integrable : ∀ x, IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume 0 T
  pde : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
    u s x-u t x = -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (u r)) x+γ r*(u r x*deriv (u r) x))
  initial : u 0 0=0

noncomputable def gradientMeshError (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z, (u T (euler T N γ u z N)-∑ i : Fin N,
    Real.sqrt (stepSize T N)*deriv (u (meshTime T N i)) (euler T N γ u z i)*coordinate N i z)^2
    ∂gaussianProduct (Fin (N+1))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientErrorConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

noncomputable def gradientErrorConstant (T K L : ℝ) (γ : ℝ → ℝ) : ℝ :=
  T/2*K^2*gaussianSquareVariance+4*T^2*cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
    4*K^2*(γ T-γ 0)^2

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_FiniteRounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

noncomputable def finiteRounded {N : ℕ} (U : (Fin (N+1) → ℝ) → ℝ) :
    (Fin (N+1) → ℝ) → ℝ :=
  fun z ↦ Real.sign (U z+2*cdf standardGaussian (coordinate N N z)-1)

noncomputable def finiteRawMartingale {N : ℕ} (δ : ℝ)
    (H : Fin N → (Fin (N+1) → ℝ) → ℝ) : (Fin (N+1) → ℝ) → ℝ :=
  fun z ↦ ∑ i : Fin N, Real.sqrt δ * H i z * coordinate N i z

end SKValue

open Filter Set
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

noncomputable def meshRaw (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  deriv (u (meshTime T N j)) (euler T N γ u z j)

noncomputable def meshTerminal (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : ℝ := u T (euler T N γ u z N)

noncomputable def meshA (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) : ℝ :=
  ∫ z, finiteRounded (meshTerminal T N γ u) z *
    normalizedIncrement (meshRaw T N γ u j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
    ∂gaussianProduct (Fin (N+1))

noncomputable def meshB (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) : ℝ :=
  ∫ z, finiteRounded (meshTerminal T N γ u) z * coordinate N j z ∂gaussianProduct (Fin (N+1))

noncomputable def finiteShiftedValue (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : ℝ :=
  ∑ i : Fin N, meshA T N γ u i * meshB T N γ u (i+1)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BrownianIncrementIndepPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology NNReal ENNReal BigOperators

noncomputable def driftDefect (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (X W : ℝ → ℝ) : ℝ :=
  ∑ i : Fin N, |X (meshTime T N (i+1))-X (meshTime T N i)-
    (W (meshTime T N (i+1))-W (meshTime T N i))-
    stepSize T N*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStripCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

structure GradientStripCore (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (K L : ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0 : ℝ) T)
  smooth : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 3 (u t)
  bounded : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x|≤1
  second_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (deriv (u t)) x|≤K
  third_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |iteratedDeriv 3 (u t) x|≤K
  product_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x*deriv (u t) x|≤K
  second_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |deriv (deriv (u s)) y-deriv (deriv (u t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |u s y*deriv (u s) y-u t x*deriv (u t) x|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ x, IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume 0 T
  product_integrable : ∀ x, IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume 0 T
  pde : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
    u s x-u t x = -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (u r)) x+γ r*(u r x*deriv (u r) x))

noncomputable def pathGradientResidual (T : ℝ) (N : ℕ) (u : ℝ → ℝ → ℝ)
    (X W : ℝ → ℝ) : ℝ :=
  u T (X T)-u 0 (X 0)-∑ i : Fin N,
    deriv (u (meshTime T N i)) (X (meshTime T N i))*
      (W (meshTime T N (i+1))-W (meshTime T N i))-
    (1/2 : ℝ)*∑ i : Fin N,
      deriv (deriv (u (meshTime T N i))) (X (meshTime T N i))*
        ((W (meshTime T N (i+1))-W (meshTime T N i))^2-stepSize T N)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_CubicEnvelopeMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

noncomputable def cubicEnvelopeMean (G K C : ℝ) : ℝ :=
  ∫ z : ℝ, cubicEnvelope G K C z ∂standardGaussian

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ColeHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def heat (h : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, ψ (x+Real.sqrt h*z) ∂standardGaussian

noncomputable def coleHopf (c h : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if c=0 then heat h ψ x else Real.log (heat h (fun y ↦ Real.exp (c*ψ y)) x)/c

lemma density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y^2/2) (-x) x := by
    have hh := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
    simpa only [Pi.pow_def,Pi.neg_def,id_eq,pow_one,show (2 : ℕ)-1=1 from rfl,
      Nat.cast_ofNat,mul_one,neg_div,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hd := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hd using 1 <;> try rfl
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    ring

lemma density_mul_integrable {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x*f x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x ↦ gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma gaussian_exp_abs_integrable (a : ℝ) :
    Integrable (fun z ↦ Real.exp (a* |z|)) standardGaussian := by
  have hi := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-a))
  apply hi.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-a*z)]
  · rw [abs_of_nonpos hz]
    have hid : a*(-z)=(-a)*z := by ring
    rw [hid]
    linarith [Real.exp_pos (a*z)]

lemma lipschitz_exp_bound {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0 ≤ c) (x y z s : ℝ) :
    Real.exp (c*ψ (y+s*z)) ≤
      Real.exp (c*(ψ x+|y-x|+|s| * |z|)) := by
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hc
  have hh := hψ.dist_le_mul (y+s*z) x
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hh
  have ha : |y+s*z-x|≤|y-x|+|s| * |z| := by
    rw [show y+s*z-x = (y-x)+s*z by ring]
    simpa only [abs_mul] using abs_add_le (y-x) (s*z)
  have hb := le_abs_self (ψ (y+s*z)-ψ x)
  linarith

lemma lipschitz_exp_integrable {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0 ≤ c) (x s : ℝ) :
    Integrable (fun z ↦ Real.exp (c*ψ (x+s*z))) standardGaussian := by
  have hi := (gaussian_exp_abs_integrable (c* |s|)).const_mul (Real.exp (c*ψ x))
  have hψc := hψ.continuous
  apply hi.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hh := lipschitz_exp_bound hψ hc x x z s
  simpa only [sub_self,abs_zero,add_zero,mul_add,Real.exp_add,mul_assoc] using hh

lemma lipschitz_exp_integral_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0 ≤ c) (x s : ℝ) :
    0 < ∫ z, Real.exp (c*ψ (x+s*z)) ∂standardGaussian :=
  integral_exp_pos (lipschitz_exp_integrable hψ hc x s)

lemma gaussian_stein_of_integrable {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hfi : Integrable f standardGaussian)
    (hf'i : Integrable f' standardGaussian)
    (hxfi : Integrable (fun x ↦ x*f x) standardGaussian) :
    (∫ x, x*f x ∂standardGaussian) = ∫ x, f' x ∂standardGaussian := by
  have hi1 : Integrable (fun x ↦ f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert (density_mul_integrable hxfi).neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x ↦ f' x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hf'i
  have hi3 : Integrable (fun x ↦ f x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hfi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x ↦ -x*gaussianPDFReal 0 1 x)
    (fun x _ ↦ hf x) (fun x _ ↦ density_hasDerivAt x) hi1 hi2 hi3
  have hb : (∫ x, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by ring)
  rw [hb] at hibp
  have he : (∫ x, gaussianPDFReal 0 1 x*(x*f x)) =
      ∫ x, gaussianPDFReal 0 1 x*f' x := by
    exact neg_injective hibp |>.trans (by congr 1; funext x; ring)
  simpa only [standardGaussian,integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul] using he

lemma exponential_heat_hasDerivAt {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) {c : ℝ} (hc : 0 ≤ c) (x s : ℝ) :
    HasDerivAt (fun y ↦ ∫ z, Real.exp (c*ψ (y+s*z)) ∂standardGaussian)
      (∫ z, Real.exp (c*ψ (x+s*z))*(c*deriv ψ (x+s*z)) ∂standardGaussian) x := by
  have hψc := hψ.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψd := hψs.differentiable (by norm_num)
  let bd := fun z ↦ c*Real.exp (c*(ψ x+1))*Real.exp ((c* |s|)* |z|)
  have hbi : Integrable bd standardGaussian :=
    (gaussian_exp_abs_integrable (c* |s|)).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y z ↦ Real.exp (c*ψ (y+s*z)))
    (F' := fun y z ↦ Real.exp (c*ψ (y+s*z))*(c*deriv ψ (y+s*z)))
    (s := Metric.ball x 1) (bound := bd) (by exact Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun y ↦ by fun_prop))
    (lipschitz_exp_integrable hψ hc x s) (by fun_prop) _ hbi _).2
  · filter_upwards [] with z
    intro y hy
    have hyd : |y-x|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.le
    have hd : |deriv ψ (y+s*z)|≤1 := by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y+s*z)
    have hex := lipschitz_exp_bound hψ hc x y z s
    have hex' : Real.exp (c*ψ (y+s*z)) ≤
        Real.exp (c*(ψ x+1+|s| * |z|)) :=
      hex.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hc))
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul,abs_of_nonneg hc]
    calc
      _ ≤ Real.exp (c*ψ (y+s*z))*(c*1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hc) (Real.exp_pos _).le
      _ ≤ c*Real.exp (c*(ψ x+1+|s| * |z|)) := by
        simpa only [mul_one,one_mul,mul_comm c] using mul_le_mul_of_nonneg_left hex' hc
      _ = bd z := by simp only [bd,mul_add,Real.exp_add,mul_assoc]
  · filter_upwards [] with z
    intro y _
    have hh := (((hψd (y+s*z)).hasDerivAt.comp y ((hasDerivAt_id y).add_const (s*z))).const_mul c).exp
    simpa only [mul_one,Function.comp_def,id_eq] using hh

lemma coleHopf_hasDerivAt_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) {c : ℝ} (hc : 0 < c) (h x : ℝ) :
    HasDerivAt (coleHopf c h ψ)
      ((∫ z, Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z) ∂standardGaussian)/
        heat h (fun y ↦ Real.exp (c*ψ y)) x) x := by
  have hp := lipschitz_exp_integral_pos hψ hc.le x (Real.sqrt h)
  have hh := ((exponential_heat_hasDerivAt hψ hψs hc.le x (Real.sqrt h)).log hp.ne').div_const c
  have hf : coleHopf c h ψ = fun y ↦
      Real.log (∫ z, Real.exp (c*ψ (y+Real.sqrt h*z)) ∂standardGaussian)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',heat]
  rw [hf]
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [show (fun z ↦ Real.exp (c*ψ (x+Real.sqrt h*z))*(c*deriv ψ (x+Real.sqrt h*z))) =
      fun z ↦ c*(Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z)) by
        funext z; ring, integral_const_mul]
  dsimp only [heat]
  field_simp [hc.ne',hp.ne']

lemma coleHopf_deriv_bound_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) {c : ℝ} (hc : 0 < c) (h x : ℝ) :
    |deriv (coleHopf c h ψ) x|≤1 := by
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ' (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hfi := lipschitz_exp_integrable hψ hc.le x (Real.sqrt h)
  have hf'i : Integrable (fun z ↦ Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z))
      standardGaussian := hfi.mul_bdd (by fun_prop)
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hψ' (x+Real.sqrt h*z)))
  have hib : |∫ z, Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z) ∂standardGaussian| ≤
      ∫ z, Real.exp (c*ψ (x+Real.sqrt h*z)) ∂standardGaussian := by
    apply abs_integral_le_integral_abs.trans
    apply integral_mono hf'i.abs hfi
    intro z
    simpa only [abs_mul,abs_of_pos (Real.exp_pos _),mul_one] using
      mul_le_mul_of_nonneg_left (hψ' (x+Real.sqrt h*z)) (Real.exp_pos _).le
  rw [(coleHopf_hasDerivAt_of_pos hψ hψs hc h x).deriv,abs_div,heat,
    abs_of_pos (lipschitz_exp_integral_pos hψ hc.le x (Real.sqrt h))]
  exact (div_le_one (lipschitz_exp_integral_pos hψ hc.le x (Real.sqrt h))).mpr hib

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

def ExpGrowth (f : ℝ → ℝ) : Prop :=
  ∃ a C : ℝ, 0≤a ∧ 0≤C ∧ ∀ x, |f x|≤C*Real.exp (a* |x|)

lemma gaussian_abs_mul_exp_integrable (a : ℝ) :
    Integrable (fun z ↦ |z| * Real.exp (a* |z|)) standardGaussian := by
  apply (gaussian_exp_abs_integrable (a+1)).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp |z| * Real.exp (a* |z|) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp |z|]) (Real.exp_pos _).le
    _ = Real.exp ((a+1)* |z|) := by rw [←Real.exp_add]; congr 1; ring

lemma expGrowth_shift_bound {f : ℝ → ℝ} {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hf : ∀ y, |f y|≤C*Real.exp (a* |y|)) (x s z : ℝ) :
    |f (x+s*z)|≤(C*Real.exp (a* |x|))*Real.exp ((a* |s|)* |z|) := by
  apply (hf _).trans
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have hh := abs_add_le x (s*z)
  rw [abs_mul] at hh
  nlinarith

lemma ExpGrowth.shift_integrable {f : ℝ → ℝ} (hf : ExpGrowth f)
    (hm : Measurable f) (x s : ℝ) :
    Integrable (fun z ↦ f (x+s*z)) standardGaussian := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  apply ((gaussian_exp_abs_integrable (a* |s|)).const_mul (C*Real.exp (a* |x|))).mono' ((hm.comp (by fun_prop)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (expGrowth_shift_bound ha hC hf x s z))

lemma ExpGrowth.shift_mul_integrable {f : ℝ → ℝ} (hf : ExpGrowth f)
    (hm : Measurable f) (x s : ℝ) :
    Integrable (fun z ↦ z*f (x+s*z)) standardGaussian := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  apply ((gaussian_abs_mul_exp_integrable (a* |s|)).const_mul (C*Real.exp (a* |x|))).mono' (by exact (measurable_id.mul (hm.comp (by fun_prop))).aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_mul]
  simpa only [mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left (expGrowth_shift_bound ha hC hf x s z) (abs_nonneg z)

lemma gaussian_shift_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : Continuous f') (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x s : ℝ) :
    HasDerivAt (fun y ↦ ∫ z, f (y+s*z) ∂standardGaussian)
      (∫ z, f' (x+s*z) ∂standardGaussian) x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y ↦ (hf y).continuousAt)
  obtain ⟨a,C,ha,hC,hg⟩ := hf'g
  let bd := fun z ↦ (C*Real.exp (a*(|x|+1)))*Real.exp ((a* |s|)* |z|)
  have hbi : Integrable bd standardGaussian :=
    (gaussian_exp_abs_integrable (a* |s|)).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y z ↦ f (y+s*z)) (F' := fun y z ↦ f' (y+s*z))
    (s := Metric.ball x 1) (bound := bd) (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun _ ↦ by fun_prop)) (hfg.shift_integrable hfc.measurable x s)
    (by fun_prop) _ hbi _).2
  · filter_upwards [] with z
    intro y hy
    have hyd : |y-x|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.le
    have hab : |y|≤|x|+1 := by
      have hh := abs_add_le (y-x) x
      rw [sub_add_cancel] at hh
      linarith
    rw [Real.norm_eq_abs]
    apply (expGrowth_shift_bound ha hC hg y s z).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab ha)) hC)
      (Real.exp_pos _).le
  · filter_upwards [] with z
    intro y _
    simpa only [Function.comp_def,id_eq,mul_one] using
      ((hf (y+s*z)).comp y ((hasDerivAt_id y).add_const (s*z)))

lemma gaussian_scale_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : Continuous f') (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x s : ℝ) :
    HasDerivAt (fun r ↦ ∫ z, f (x+r*z) ∂standardGaussian)
      (∫ z, z*f' (x+s*z) ∂standardGaussian) s := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y ↦ (hf y).continuousAt)
  obtain ⟨a,C,ha,hC,hg⟩ := hf'g
  let bd := fun z ↦ (C*Real.exp (a* |x|))*(|z| * Real.exp ((a*(|s|+1))* |z|))
  have hbi : Integrable bd standardGaussian :=
    (gaussian_abs_mul_exp_integrable (a*(|s|+1))).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r z ↦ f (x+r*z)) (F' := fun r z ↦ z*f' (x+r*z))
    (s := Metric.ball s 1) (bound := bd) (Metric.ball_mem_nhds s (by norm_num))
    (Eventually.of_forall (fun _ ↦ by fun_prop)) (hfg.shift_integrable hfc.measurable x s)
    (by fun_prop) _ hbi _).2
  · filter_upwards [] with z
    intro r hr
    have hrd : |r-s|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hr.le
    have hab : |r|≤|s|+1 := by
      have hh := abs_add_le (r-s) s
      rw [sub_add_cancel] at hh
      linarith
    rw [Real.norm_eq_abs,abs_mul]
    apply (mul_le_mul_of_nonneg_left (expGrowth_shift_bound ha hC hg x r z) (abs_nonneg z)).trans
    have hex : Real.exp ((a* |r|)* |z|)≤Real.exp ((a*(|s|+1))* |z|) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab ha) (abs_nonneg z))
    have hh := mul_le_mul_of_nonneg_left hex (by positivity : 0≤|z| * (C*Real.exp (a* |x|)))
    dsimp only [bd]
    nlinarith
  · filter_upwards [] with z
    intro r _
    have hh := (hf (x+r*z)).comp r (((hasDerivAt_id r).mul_const z).const_add x)
    simpa only [Function.comp_def,id_eq,one_mul,mul_one,mul_comm] using hh

lemma gaussian_scale_deriv_eq {f f' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : Continuous f')
    (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x s : ℝ) :
    (∫ z, z*f (x+s*z) ∂standardGaussian) = s*(∫ z, f' (x+s*z) ∂standardGaussian) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y ↦ (hf y).continuousAt)
  have hh := gaussian_stein_of_integrable
    (f := fun z ↦ f (x+s*z)) (f' := fun z ↦ s*f' (x+s*z))
    (fun z ↦ by
      have hd := (hf (x+s*z)).comp z (((hasDerivAt_id z).const_mul s).const_add x)
      simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using hd)
    (hfg.shift_integrable hfc.measurable x s)
    ((hf'g.shift_integrable hf'.measurable x s).const_mul s)
    (hfg.shift_mul_integrable hfc.measurable x s)
  simpa only [integral_const_mul] using hh

lemma heat_time_hasDerivAt {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') (x : ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun r ↦ heat r f x) ((1/2 : ℝ)*heat h f'' x) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := (gaussian_scale_hasDerivAt hf hf'c hfg hf'g x (Real.sqrt h)).comp h
    (Real.hasDerivAt_sqrt hh.ne')
  rw [gaussian_scale_deriv_eq hf' hf'' hf'g hf''g x (Real.sqrt h)] at hd
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [heat]
  field_simp [Real.sqrt_ne_zero'.mpr hh]

lemma heat_spatial_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : Continuous f')
    (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x h : ℝ) :
    HasDerivAt (heat h f) (heat h f' x) x :=
  gaussian_shift_hasDerivAt hf hf' hfg hf'g x (Real.sqrt h)

lemma heat_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f)
    (hg : ∀ n : ℕ, ExpGrowth (iteratedDeriv n f)) (h : ℝ) (n : ℕ) :
    iteratedDeriv n (heat h f) = heat h (iteratedDeriv n f) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (heat_spatial_hasDerivAt
      (fun y ↦ by simpa only [iteratedDeriv_succ] using
        ((hf.differentiable_iteratedDeriv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) y).hasDerivAt)
      (hf.continuous_iteratedDeriv (n+1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))) (hg n) (hg (n+1)) x h).deriv

lemma heat_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f)
    (hg : ∀ n : ℕ, ExpGrowth (iteratedDeriv n f)) (h : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (heat h f) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro n _
  rw [heat_iteratedDeriv hf hg]
  intro x
  exact (heat_spatial_hasDerivAt
    (fun y ↦ by simpa only [iteratedDeriv_succ] using
      ((hf.differentiable_iteratedDeriv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) y).hasDerivAt)
    (hf.continuous_iteratedDeriv (n+1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))) (hg n) (hg (n+1)) x h).differentiableAt

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ColeHopfPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_log_spatial_deriv {f f' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : Continuous f')
    (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (c h : ℝ)
    (hp : ∀ x, heat h f x ≠ 0) :
    deriv (fun x ↦ Real.log (heat h f x)/c) = fun x ↦ (heat h f' x/heat h f x)/c := by
  funext x
  exact (((heat_spatial_hasDerivAt hf hf' hfg hf'g x h).log (hp x)).div_const c).deriv

lemma heat_log_spatial_second {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') (c h : ℝ) (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x =
      ((heat h f'' x*heat h f x-heat h f' x*heat h f' x)/(heat h f x)^2)/c := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  rw [heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  exact (((heat_spatial_hasDerivAt hf' hf'' hf'g hf''g x h).div
    (heat_spatial_hasDerivAt hf hf'c hfg hf'g x h) (hp x)).div_const c).deriv

lemma ExpGrowth.mul_bounded {f g : ℝ → ℝ} (hf : ExpGrowth f)
    {R : ℝ} (hR : 0≤R) (hg : ∀ x, |g x|≤R) : ExpGrowth (fun x ↦ f x*g x) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  refine ⟨a,C*R,ha,mul_nonneg hC hR,?_⟩
  intro x
  rw [abs_mul]
  calc
    _ ≤ (C*Real.exp (a* |x|))*R := mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma ExpGrowth.exp_lipschitz {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0 ≤ c) : ExpGrowth (fun x ↦ Real.exp (c*ψ x)) := by
  refine ⟨c,Real.exp (c*ψ 0),hc,(Real.exp_pos _).le,?_⟩
  intro x
  rw [abs_of_pos (Real.exp_pos _),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hψ.dist_le_mul x 0
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero] at hh
  have hx := le_abs_self (ψ x-ψ 0)
  nlinarith

lemma ExpGrowth.of_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0≤C) (hf : ∀ x, |f x|≤C) :
    ExpGrowth f := by
  refine ⟨0,C,le_rfl,hC,?_⟩
  intro x
  simpa only [zero_mul,Real.exp_zero,mul_one] using hf x

lemma ExpGrowth.lipschitz {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) : ExpGrowth ψ := by
  refine ⟨1,|ψ 0|+1,by norm_num,by positivity,?_⟩
  intro x
  have hh := hψ.dist_le_mul x 0
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero] at hh
  have hu : |ψ x|≤|ψ 0|+|x| := by
    have hh2 := abs_add_le (ψ x-ψ 0) (ψ 0)
    rw [sub_add_cancel] at hh2
    linarith
  rw [one_mul]
  have he1 : 1≤Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  have he2 : |x|≤Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  nlinarith [mul_le_mul_of_nonneg_left he1 (abs_nonneg (ψ 0))]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_BoundedSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

structure BoundedSmooth (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  bound : ∀ n : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ x, |iteratedDeriv n f x|≤C

lemma BoundedSmooth.bound_zero {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |f x|≤C := by
  simpa only [iteratedDeriv_zero] using hf.bound 0

lemma BoundedSmooth.const (c : ℝ) : BoundedSmooth (fun _ : ℝ ↦ c) := by
  refine ⟨contDiff_const,fun n ↦ ⟨|c|,abs_nonneg c,?_⟩⟩
  intro x
  by_cases hn : n=0
  · subst n; simp only [iteratedDeriv_zero,le_refl]
  · simp only [iteratedDeriv_const,ite_eq_right hn,abs_zero,abs_nonneg]

lemma BoundedSmooth.deriv {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    BoundedSmooth (deriv f) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hf.smooth).2,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using hf.bound (n+1)

lemma BoundedSmooth.add {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x+g x) := by
  refine ⟨hf.smooth.add hg.smooth,?_⟩
  intro n
  obtain ⟨A,hA,hfA⟩ := hf.bound n
  obtain ⟨B,hB,hgB⟩ := hg.bound n
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro x
  rw [iteratedDeriv_fun_add
    (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
  exact (abs_add_le _ _).trans (add_le_add (hfA x) (hgB x))

lemma BoundedSmooth.mul {f g : ℝ → ℝ} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x*g x) := by
  classical
  choose A hA hfA using hf.bound
  choose B hB hgB using hg.bound
  refine ⟨hf.smooth.mul hg.smooth,?_⟩
  intro n
  refine ⟨∑ i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i),?_,?_⟩
  · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))
  · intro x
    rw [iteratedDeriv_fun_mul
      (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
      (hg.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hfA i x) (Nat.cast_nonneg _)) (hgB (n-i) x)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))

lemma BoundedSmooth.const_mul {f : ℝ → ℝ} (hf : BoundedSmooth f) (c : ℝ) :
    BoundedSmooth (fun x ↦ c*f x) := (BoundedSmooth.const c).mul hf

noncomputable def expJet (c : ℝ) (ψ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ ↦ 1
  | n+1 => fun x ↦ deriv (expJet c ψ n) x+expJet c ψ n x*(c*deriv ψ x)

lemma expJet_boundedSmooth {ψ : ℝ → ℝ} (hψ : BoundedSmooth (deriv ψ)) (c : ℝ) (n : ℕ) :
    BoundedSmooth (expJet c ψ n) := by
  induction n with
  | zero => exact BoundedSmooth.const 1
  | succ n ih => exact ih.deriv.add (ih.mul (hψ.const_mul c))

lemma exp_iteratedDeriv {ψ : ℝ → ℝ} (hψs : ContDiff ℝ ∞ ψ)
    (hψ : BoundedSmooth (deriv ψ)) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)) =
      fun x ↦ Real.exp (c*ψ x)*expJet c ψ n x := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,expJet,mul_one]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hψd := hψs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))
    have hJd := (expJet_boundedSmooth hψ c n).smooth.differentiable
      (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))
    have hd := (((hψd x).hasDerivAt.const_mul c).exp).mul (hJd x).hasDerivAt
    convert! hd.deriv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [expJet]
    ring

lemma exp_iteratedDeriv_growth {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ExpGrowth (iteratedDeriv n (fun x ↦ Real.exp (c*ψ x))) := by
  rw [exp_iteratedDeriv hψs hψ c n]
  obtain ⟨C,hC,hJ⟩ := (expJet_boundedSmooth hψ c n).bound_zero
  exact (ExpGrowth.exp_lipschitz hψl hc).mul_bounded hC hJ

lemma coleHopf_contDiff_of_pos {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0 < c) (h : ℝ) :
    ContDiff ℝ ∞ (coleHopf c h ψ) := by
  have he : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  have hH := heat_contDiff he (exp_iteratedDeriv_growth hψl hψs hψ hc.le) h
  have hp (x : ℝ) : heat h (fun y ↦ Real.exp (c*ψ y)) x ≠0 :=
    (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt h)).ne'
  have heq : coleHopf c h ψ = fun x ↦ Real.log (heat h (fun y ↦ Real.exp (c*ψ y)) x)/c := by
    funext x
    simp only [coleHopf,ite_eq_right hc.ne']
  rw [heq]
  exact (hH.log hp).div_const c

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

lemma derivative_tower_bounded {ι : Type*} (R : ℕ → ι → ℝ → ℝ)
    (hs : ∀ j a, ContDiff ℝ ∞ (R j a))
    (hd : ∀ j a, deriv (R j a) = fun x ↦ R (j+1) a x-R j a x*R 1 a x)
    (hb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a x, |R j a x|≤C) :
    ∀ n j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ a x, |iteratedDeriv n (R j a) x|≤C := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => intro j; simpa only [iteratedDeriv_zero] using hb j
    | succ n =>
      have hlo : ∀ k j : ℕ, ∃ C : ℝ, 0≤C ∧
          (k≤n → ∀ a x, |iteratedDeriv k (R j a) x|≤C) := by
        intro k j
        by_cases hk : k≤n
        · obtain ⟨C,hC,hbC⟩ := ih k (Nat.lt_succ_of_le hk) j
          exact ⟨C,hC,fun _ ↦ hbC⟩
        · exact ⟨0,le_rfl,fun h ↦ (hk h).elim⟩
      choose C hC hbound using hlo
      intro j
      refine ⟨C n (j+1)+∑ k∈Finset.range (n+1), (n.choose k : ℝ)*C k j*C (n-k) 1,?_,?_⟩
      · exact add_nonneg (hC _ _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _ _)) (hC _ _)))
      · intro a x
        rw [iteratedDeriv_succ',hd,
          iteratedDeriv_fun_sub
            ((hs (j+1) a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            (((hs j a).mul (hs 1 a)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
          iteratedDeriv_fun_mul
            ((hs j a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            ((hs 1 a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
        apply (abs_sub _ _).trans
        apply add_le_add (hbound n (j+1) le_rfl a x)
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound k j hk' a x) (Nat.cast_nonneg _))
          (hbound (n-k) 1 (Nat.sub_le ..) a x) (abs_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hC _ _))

noncomputable def normalizedJet {ι : Type*} (F : ι → ℝ → ℝ) (j : ℕ) (a : ι) (x : ℝ) : ℝ :=
  iteratedDeriv j (F a) x/F a x

lemma normalizedJet_smooth {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0) (j : ℕ) (a : ι) :
    ContDiff ℝ ∞ (normalizedJet F j a) :=
  (smooth_iteratedDeriv (hs a) j).div (hs a) (hp a)

lemma normalizedJet_deriv {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0) (j : ℕ) (a : ι) :
    deriv (normalizedJet F j a) =
      fun x ↦ normalizedJet F (j+1) a x-normalizedJet F j a x*normalizedJet F 1 a x := by
  funext x
  have hd := (((hs a).differentiable_iteratedDeriv j
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)) x).hasDerivAt
  have hF := (((hs a).differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))) x).hasDerivAt
  change deriv (fun y ↦ iteratedDeriv j (F a) y/F a y) x = _
  convert! (hd.div hF (hp a x)).deriv using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [normalizedJet]
  rw [iteratedDeriv_succ,iteratedDeriv_one]
  field_simp [hp a x]

lemma normalizedJet_uniform_bounded {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0)
    (hb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a x, |normalizedJet F j a x|≤C) :
    ∀ n j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ a x, |iteratedDeriv n (normalizedJet F j a) x|≤C :=
  derivative_tower_bounded (normalizedJet F) (normalizedJet_smooth hs hp)
    (normalizedJet_deriv hs hp) hb

lemma normalizedJet_boundedSmooth {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0)
    (hb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a x, |normalizedJet F j a x|≤C) (j : ℕ) (a : ι) :
    BoundedSmooth (normalizedJet F j a) := by
  refine ⟨normalizedJet_smooth hs hp j a,?_⟩
  intro n
  obtain ⟨C,hC,hbC⟩ := normalizedJet_uniform_bounded hs hp hb n j
  exact ⟨C,hC,hbC a⟩

lemma heat_relative_bound {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : ExpGrowth f) (hgg : ExpGrowth g) {C : ℝ}
    (hb : ∀ x, |g x|≤C*f x) (h x : ℝ) :
    |heat h g x|≤C*heat h f x := by
  apply abs_integral_le_integral_abs.trans
  rw [heat,←integral_const_mul]
  apply integral_mono (hgg.shift_integrable hg x (Real.sqrt h)).abs
    ((hfg.shift_integrable hf x (Real.sqrt h)).const_mul C)
  exact fun z ↦ hb _

lemma exp_heat_normalizedJet_bound {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0 ≤ c) :
    ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ h x,
      |normalizedJet (fun t ↦ heat t (fun y ↦ Real.exp (c*ψ y))) j h x|≤C := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  have heg := exp_iteratedDeriv_growth hψl hψs hψ hc
  intro j
  obtain ⟨C,hC,hJ⟩ := (expJet_boundedSmooth hψ c j).bound_zero
  refine ⟨C,hC,?_⟩
  intro h x
  dsimp only [normalizedJet]
  rw [heat_iteratedDeriv hes heg,abs_div]
  have hp : 0 < heat h (fun y ↦ Real.exp (c*ψ y)) x :=
    lipschitz_exp_integral_pos hψl hc x (Real.sqrt h)
  rw [abs_of_pos hp]
  apply (div_le_iff₀ (lipschitz_exp_integral_pos hψl hc x (Real.sqrt h))).mpr
  exact heat_relative_bound hes.continuous.measurable
    (smooth_iteratedDeriv hes j).continuous.measurable
    (ExpGrowth.exp_lipschitz hψl hc) (heg j)
    (fun y ↦ by
      rw [exp_iteratedDeriv hψs hψ c j,abs_mul,abs_of_pos (Real.exp_pos _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hJ y) (Real.exp_pos (c*ψ y)).le) h x

lemma coleHopf_deriv_eq_normalizedJet {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0 < c) (h : ℝ) :
    deriv (coleHopf c h ψ) = fun x ↦
      c⁻¹*normalizedJet (fun t ↦ heat t (fun y ↦ Real.exp (c*ψ y))) 1 h x := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  have hHs := heat_contDiff hes (exp_iteratedDeriv_growth hψl hψs hψ hc.le) h
  have heq : coleHopf c h ψ = fun x ↦ Real.log (heat h (fun y ↦ Real.exp (c*ψ y)) x)/c := by
    funext x
    simp only [coleHopf,ite_eq_right hc.ne']
  rw [heq]
  funext x
  have hHd := ((hHs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))) x).hasDerivAt
  have hd := (hHd.log (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt h)).ne').div_const c
  convert! hd.deriv using 1
  all_goals try with_reducible_and_instances rfl
  simp only [normalizedJet,iteratedDeriv_one,div_eq_mul_inv]
  ring

lemma coleHopf_deriv_boundedSmooth_of_pos {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0 < c) (h : ℝ) :
    BoundedSmooth (deriv (coleHopf c h ψ)) := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  rw [coleHopf_deriv_eq_normalizedJet hψl hψs hψ hc h]
  exact (normalizedJet_boundedSmooth
    (fun t ↦ heat_contDiff hes (exp_iteratedDeriv_growth hψl hψs hψ hc.le) t)
    (fun t x ↦ (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt t)).ne')
    (exp_heat_normalizedJet_bound hψl hψs hψ hc.le) 1 h).const_mul _

lemma coleHopf_deriv_uniform_bounds_of_pos {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0 < c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  intro n
  obtain ⟨C,hC,hb⟩ := normalizedJet_uniform_bounded
    (fun t ↦ heat_contDiff hes (exp_iteratedDeriv_growth hψl hψs hψ hc.le) t)
    (fun t x ↦ (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt t)).ne')
    (exp_heat_normalizedJet_bound hψl hψs hψ hc.le) n 1
  refine ⟨|c⁻¹| * C,by positivity,?_⟩
  intro h x
  rw [coleHopf_deriv_eq_normalizedJet hψl hψs hψ hc h,iteratedDeriv_const_mul_field,abs_mul]
  exact mul_le_mul_of_nonneg_left (hb h x) (abs_nonneg _)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma gaussian_shift_continuous {f : ℝ → ℝ} (hfc : Continuous f) (hfg : ExpGrowth f) :
    Continuous (fun p : ℝ×ℝ ↦ ∫ z, f (p.1+p.2*z) ∂standardGaussian) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hfg
  apply continuous_iff_continuousAt.mpr
  intro p
  let bd := fun z ↦ (C*Real.exp (a*(|p.1|+1)))*Real.exp ((a*(|p.2|+1))* |z|)
  apply tendsto_integral_filter_of_dominated_convergence bd
    (Eventually.of_forall (fun q ↦ by fun_prop)) _
    ((gaussian_exp_abs_integrable (a*(|p.2|+1))).const_mul _) _
  · filter_upwards [Metric.ball_mem_nhds p (by norm_num : (0 : ℝ)<1)] with q hq
    have hq' : |q.1-p.1|<1 ∧ |q.2-p.2|<1 := by
      simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,max_lt_iff] using hq
    have hq1 : |q.1|≤|p.1|+1 := by
      have hh := abs_add_le (q.1-p.1) p.1
      rw [sub_add_cancel] at hh
      linarith [hq'.1]
    have hq2 : |q.2|≤|p.2|+1 := by
      have hh := abs_add_le (q.2-p.2) p.2
      rw [sub_add_cancel] at hh
      linarith [hq'.2]
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    apply (expGrowth_shift_bound ha hC hf q.1 q.2 z).trans
    dsimp only [bd]
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq1 ha)) hC)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 ha) (abs_nonneg z)))
      (Real.exp_pos _).le (by positivity)
  · exact Eventually.of_forall (fun z ↦ (hfc.comp (continuous_fst.add (continuous_snd.mul continuous_const))).continuousAt)

lemma heat_continuous {f : ℝ → ℝ} (hfc : Continuous f) (hfg : ExpGrowth f) :
    Continuous (fun p : ℝ×ℝ ↦ heat p.1 f p.2) := by
  exact (gaussian_shift_continuous hfc hfg).comp
    (continuous_snd.prodMk (Real.continuous_sqrt.comp continuous_fst))

@[simp] lemma heat_zero (f : ℝ → ℝ) (x : ℝ) : heat 0 f x=f x := by
  simp [heat]

@[simp] lemma coleHopf_zero_coeff (h : ℝ) (ψ : ℝ → ℝ) : coleHopf 0 h ψ=heat h ψ := by
  funext x
  simp [coleHopf]

@[simp] lemma coleHopf_zero (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : coleHopf c 0 ψ x=ψ x := by
  by_cases hc : c=0
  · simp [coleHopf,hc]
  · simp [coleHopf,hc,Real.log_exp]

lemma heat_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0≤C) (hf : ∀ x, |f x|≤C) (h x : ℝ) :
    |heat h f x|≤C := by
  unfold heat
  by_cases hfi : Integrable (fun z ↦ f (x+Real.sqrt h*z)) standardGaussian
  · apply abs_integral_le_integral_abs.trans
    convert integral_mono hfi.abs
      (integrable_const C : Integrable (fun _ : ℝ ↦ C) standardGaussian)
      (fun z ↦ hf (x+Real.sqrt h*z)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  · simpa only [integral_undef hfi,abs_zero] using hC

structure SmoothTerminal (ψ : ℝ → ℝ) : Prop where
  lipschitz : LipschitzWith 1 ψ
  smooth : ContDiff ℝ ∞ ψ
  jets : BoundedSmooth (deriv ψ)

lemma SmoothTerminal.growth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (n : ℕ) :
    ExpGrowth (iteratedDeriv n ψ) := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using ExpGrowth.lipschitz hψ.lipschitz
  | succ n =>
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    rw [iteratedDeriv_succ']
    exact ExpGrowth.of_bound hC hb

lemma SmoothTerminal.heat_smooth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (h : ℝ) :
    ContDiff ℝ ∞ (heat h ψ) := heat_contDiff hψ.smooth hψ.growth h

lemma SmoothTerminal.heat_deriv {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (h : ℝ) :
    deriv (heat h ψ)=heat h (deriv ψ) := by
  simpa only [iteratedDeriv_one] using heat_iteratedDeriv hψ.smooth hψ.growth h 1

lemma SmoothTerminal.heat_deriv_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (n : ℕ) (h : ℝ) :
    iteratedDeriv n (deriv (heat h ψ))=heat h (iteratedDeriv n (deriv ψ)) := by
  simpa only [iteratedDeriv_succ'] using heat_iteratedDeriv hψ.smooth hψ.growth h (n+1)

lemma SmoothTerminal.coleHopf_smooth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) (h : ℝ) :
    ContDiff ℝ ∞ (coleHopf c h ψ) := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [coleHopf_zero_coeff]
    exact hψ.heat_smooth h
  · exact coleHopf_contDiff_of_pos hψ.lipschitz hψ.smooth hψ.jets hc h

lemma SmoothTerminal.coleHopf_deriv_bound {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) (h x : ℝ) :
    |deriv (coleHopf c h ψ) x|≤1 := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv]
    apply heat_bound zero_le_one
    intro y
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ.lipschitz (x₀ := y)
  · exact coleHopf_deriv_bound_of_pos hψ.lipschitz
      (hψ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hc h x

lemma SmoothTerminal.evolve {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) (h : ℝ) :
    SmoothTerminal (coleHopf c h ψ) := by
  have hs := hψ.coleHopf_smooth hc h
  refine ⟨?_,hs,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)))
    intro x
    exact_mod_cast hψ.coleHopf_deriv_bound hc h x
  · rcases hc.eq_or_lt with rfl | hc
    · refine ⟨(contDiff_infty_iff_deriv.mp hs).2,?_⟩
      intro n
      obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
      refine ⟨C,hC,?_⟩
      intro x
      rw [coleHopf_zero_coeff]
      rw [hψ.heat_deriv_jets]
      exact heat_bound hC hb h x
    · exact coleHopf_deriv_boundedSmooth_of_pos hψ.lipschitz hψ.smooth hψ.jets hc h

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogHeatJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_jet_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f)) (j : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv j (heat p.1 f) p.2) := by
  simp_rw [heat_iteratedDeriv hf hg]
  exact heat_continuous (smooth_iteratedDeriv hf j).continuous (hg j)

lemma heat_jet_time {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f)) (j : ℕ) (x : ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun r ↦ iteratedDeriv j (heat r f) x)
      ((1/2 : ℝ)*iteratedDeriv (j+2) (heat h f) x) h := by
  simp_rw [heat_iteratedDeriv hf hg]
  apply heat_time_hasDerivAt (f' := iteratedDeriv (j+1) f)
  · intro y
    simpa only [iteratedDeriv_succ] using
      ((hf.differentiable_iteratedDeriv j (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)) y).hasDerivAt
  · intro y
    simpa only [show j+2=(j+1)+1 from rfl,iteratedDeriv_succ] using
      ((hf.differentiable_iteratedDeriv (j+1) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl (j+1))) y).hasDerivAt
  · exact (smooth_iteratedDeriv hf (j+2)).continuous
  · exact hg j
  · exact hg (j+1)
  · exact hg (j+2)
  · exact hh

lemma heat_normalizedJet_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f))
    (hp : ∀ h x, heat h f x≠0) (j : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ normalizedJet (fun r ↦ heat r f) j p.1 p.2) := by
  exact (heat_jet_continuous hf hg j).div
    (heat_continuous hf.continuous (by simpa only [iteratedDeriv_zero] using hg 0)) (fun p ↦ hp p.1 p.2)

lemma heat_normalizedJet_time {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ n, ExpGrowth (iteratedDeriv n f))
    (hp : ∀ h x, heat h f x≠0) (j : ℕ) (x : ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun r ↦ normalizedJet (fun s ↦ heat s f) j r x)
      ((1/2 : ℝ)*(normalizedJet (fun s ↦ heat s f) (j+2) h x-
        normalizedJet (fun s ↦ heat s f) j h x*normalizedJet (fun s ↦ heat s f) 2 h x)) h := by
  have hd := (heat_jet_time hf hg j x hh).div (heat_jet_time hf hg 0 x hh) (hp h x)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [normalizedJet]
  simp only [iteratedDeriv_zero,zero_add]
  field_simp [hp h x]

lemma coleHopf_gradient_jet_expr {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) (h : ℝ) :
    iteratedDeriv n (deriv (coleHopf c h ψ)) = fun x ↦ c⁻¹*
      JetExpr.eval (fun j ↦ normalizedJet (fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))) j h x)
        (JetExpr.logGradientJet n) := by
  let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
  have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
  have hs : ∀ r, ContDiff ℝ ∞ (F r) := fun r ↦ heat_contDiff hes hg r
  have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
  rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc h]
  funext x
  rw [iteratedDeriv_const_mul_field,
    JetExpr.iteratedDeriv_logGradientJet
      (fun j ↦ normalizedJet_smooth hs hp j h) (fun j ↦ normalizedJet_deriv hs hp j h)]

lemma SmoothTerminal.coleHopf_joint_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (coleHopf c p.1 ψ)) p.2) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp_rw [coleHopf_zero_coeff,←iteratedDeriv_succ']
    exact heat_jet_continuous hψ.smooth hψ.growth (n+1)
  · have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, heat r (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
      fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    simp_rw [coleHopf_gradient_jet_expr hψ hc]
    exact continuous_const.mul (JetExpr.continuous_eval (fun j ↦ heat_normalizedJet_continuous hes hg hp j) _)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_BurgersJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def scaledHeatJet (c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  c*iteratedDeriv n (deriv (coleHopf c t ψ)) x

lemma scaledHeatJet_expr {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) (n : ℕ) (t x : ℝ) : scaledHeatJet c ψ n t x=
    JetExpr.eval (fun j ↦ normalizedJet (fun h ↦ heat h (fun y ↦ Real.exp (c*ψ y))) j t x)
      (JetExpr.logGradientJet n) := by
  dsimp only [scaledHeatJet]
  rw [coleHopf_gradient_jet_expr hψ hc]
  simp only [←mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]

lemma scaledHeatJet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 ≤ c) (n : ℕ) : Continuous (fun p : ℝ×ℝ ↦ scaledHeatJet c ψ n p.1 p.2) :=
  continuous_const.mul (hψ.coleHopf_joint_jets hc n)

lemma scaledHeatJet_bound {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) (n : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ t x, |scaledHeatJet c ψ n t x|≤C := by
  obtain ⟨C,hC,hb⟩ := coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc n
  refine ⟨c*C,mul_nonneg hc.le hC,?_⟩
  intro t x
  dsimp only [scaledHeatJet]
  rw [abs_mul,abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hb t x) hc.le

lemma scaledHeatJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 ≤ c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (scaledHeatJet c ψ n t) (scaledHeatJet c ψ (n+1) t x) x := by
  have hs := (hψ.evolve hc t).jets.smooth
  have hd := (hs.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  exact hd.const_mul c

lemma scaledHeatJet_time_expr {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) (n : ℕ) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ n s x)
      (JetExpr.eval (fun j ↦ normalizedJet (fun h ↦ heat h (fun y ↦ Real.exp (c*ψ y))) j t x)
        (JetExpr.D JetExpr.σh (JetExpr.logGradientJet n))) t := by
  simp_rw [scaledHeatJet_expr hψ hc]
  have hes : ContDiff ℝ ∞ (fun y ↦ Real.exp (c*ψ y)) := (contDiff_const.mul hψ.smooth).exp
  have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
  have hp : ∀ h y, heat h (fun z ↦ Real.exp (c*ψ z)) y≠0 :=
    fun h y ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le y (Real.sqrt h)).ne'
  apply JetExpr.hasDerivAt_eval
  intro j
  simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x ht

namespace JetExpr
lemma burgers0 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 0))=
    (1/2 : ℝ)*eval R (logGradientJet 2)+
      eval R (logGradientJet 0)*eval R (logGradientJet 1) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring

lemma burgers1 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 1))=
    (1/2 : ℝ)*eval R (logGradientJet 3)+(eval R (logGradientJet 1))^2+
      eval R (logGradientJet 0)*eval R (logGradientJet 2) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring

lemma burgers2 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 2))=
    (1/2 : ℝ)*eval R (logGradientJet 4)+
      3*eval R (logGradientJet 1)*eval R (logGradientJet 2)+
      eval R (logGradientJet 0)*eval R (logGradientJet 3) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring

lemma burgers3 (R : ℕ → ℝ) : eval R (D σh (logGradientJet 3))=
    (1/2 : ℝ)*eval R (logGradientJet 5)+
      3*(eval R (logGradientJet 2))^2+
      4*eval R (logGradientJet 1)*eval R (logGradientJet 3)+
      eval R (logGradientJet 0)*eval R (logGradientJet 4) := by
  simp only [logGradientJet,D,σh,σx,eval]
  norm_num
  ring
end JetExpr

lemma scaledHeatJet_time0 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 0 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 2 t x+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 1 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 0 ht x
  rw [JetExpr.burgers0] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

lemma scaledHeatJet_time1 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 1 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 3 t x+(scaledHeatJet c ψ 1 t x)^2+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 2 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 1 ht x
  rw [JetExpr.burgers1] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

lemma scaledHeatJet_time2 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 2 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 4 t x+
        3*scaledHeatJet c ψ 1 t x*scaledHeatJet c ψ 2 t x+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 3 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 2 ht x
  rw [JetExpr.burgers2] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

lemma scaledHeatJet_time3 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0<t) (x : ℝ) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ 3 s x)
      ((1/2 : ℝ)*scaledHeatJet c ψ 5 t x+3*(scaledHeatJet c ψ 2 t x)^2+
        4*scaledHeatJet c ψ 1 t x*scaledHeatJet c ψ 3 t x+
        scaledHeatJet c ψ 0 t x*scaledHeatJet c ψ 4 t x) t := by
  have hd := scaledHeatJet_time_expr hψ hc 3 ht x
  rw [JetExpr.burgers3] at hd
  simpa only [scaledHeatJet_expr hψ hc] using hd

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma weighted_variance_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {w f : Ω → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<∫ x,w x ∂μ)
    (hi : Integrable w μ) (hif : Integrable (fun x ↦ w x*f x) μ)
    (his : Integrable (fun x ↦ w x*(f x)^2) μ) :
    0≤(∫ x,w x ∂μ)*(∫ x,w x*(f x)^2 ∂μ)-(∫ x,w x*f x ∂μ)^2 := by
  let Z := ∫ x,w x ∂μ
  let A := ∫ x,w x*f x ∂μ
  let J := ∫ x,w x*(f x)^2 ∂μ
  let m := A/Z
  have hm : m*Z=A := div_mul_cancel₀ A hZ.ne'
  have hs : 0≤∫ x,w x*(f x-m)^2 ∂μ := integral_nonneg (fun x ↦ mul_nonneg (hw x) (sq_nonneg _))
  have he : (∫ x,w x*(f x-m)^2 ∂μ)=J-2*m*A+m^2*Z := by
    have hp : (fun x ↦ w x*(f x-m)^2)=
        fun x ↦ w x*(f x)^2-(2*m)*(w x*f x)+m^2*w x := by funext x; ring
    rw [hp]
    have hi1 : Integrable (fun x ↦ w x * f x ^ 2 - (2*m)*(w x*f x)) μ :=
      his.sub (hif.const_mul (2*m))
    rw [integral_add hi1 (hi.const_mul (m^2))]
    rw [integral_sub his (hif.const_mul (2*m))]
    simp only [integral_const_mul]
    rfl
  rw [he] at hs
  have hz := mul_nonneg hZ.le hs
  change 0≤Z*J-A^2
  have heq : Z*(J-2*m*A+m^2*Z)=Z*J-A^2 := by rw [←hm]; ring
  rwa [heq] at hz

lemma SmoothTerminal.coleHopf_curvature_pos {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hpos : ∀ x,0<deriv (deriv ψ) x) {c : ℝ} (hc : 0 < c) (h x : ℝ) :
    0<deriv (deriv (coleHopf c h ψ)) x := by
  let f := fun y ↦ Real.exp (c*ψ y)
  let a := fun y ↦ c*deriv ψ y
  let b := fun y ↦ c*deriv (deriv ψ) y
  let f' := fun y ↦ f y*a y
  let f'' := fun y ↦ f y*((a y)^2+b y)
  have hψd := hψ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hψ'd := hψ.jets.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have ha2c : Continuous (deriv (deriv ψ)) := hψ.jets.smooth.continuous_deriv
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f,f',f'',a,b]
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ.lipschitz hc.le
  have hab (y : ℝ) : |a y| ≤ c := by
    have hh : |deriv ψ y|≤1 := by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ.lipschitz (x₀ := y)
    dsimp only [a]
    rw [abs_mul,abs_of_pos hc]
    nlinarith
  obtain ⟨K,hK,hKb⟩ := hψ.jets.bound 1
  have hbb (y : ℝ) : |b y| ≤ c*K := by
    dsimp only [b]
    rw [abs_mul,abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (by simpa only [iteratedDeriv_one] using hKb y) hc.le
  have hbg : ExpGrowth (fun y ↦ f y*b y) := hfg.mul_bounded (mul_nonneg hc.le hK) hbb
  have hag : ExpGrowth f' := hfg.mul_bounded hc.le hab
  have ha2b (y : ℝ) : |(a y)^2| ≤ c^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc.le).mpr (hab y)
  have ha2g : ExpGrowth (fun y ↦ f y*(a y)^2) := hfg.mul_bounded (sq_nonneg c) ha2b
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (add_nonneg (sq_nonneg c) (mul_nonneg hc.le hK))
    (fun y ↦ (abs_add_le _ _).trans (add_le_add (ha2b y) (hbb y)))
  have hfc : Continuous f := Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous)
  have hac : Continuous a := continuous_const.mul hψ.jets.smooth.continuous
  have hbc : Continuous b := continuous_const.mul ha2c
  have hia := hag.shift_integrable (hfc.mul hac).measurable x (Real.sqrt h)
  have hia2 := ha2g.shift_integrable (hfc.mul (hac.pow 2)).measurable x (Real.sqrt h)
  have hib := hbg.shift_integrable (hfc.mul hbc).measurable x (Real.sqrt h)
  have hi := hfg.shift_integrable hfc.measurable x (Real.sqrt h)
  have hZ : 0<heat h f x := lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt h)
  have hvar := weighted_variance_nonneg
    (w := fun z ↦ f (x+Real.sqrt h*z)) (f := fun z ↦ a (x+Real.sqrt h*z))
    (fun z ↦ (Real.exp_pos _).le) hZ hi hia hia2
  have hbpos : ∀ z,0<f (x+Real.sqrt h*z)*b (x+Real.sqrt h*z) :=
    fun z ↦ mul_pos (Real.exp_pos _) (mul_pos hc (hpos _))
  have hKpos : 0<heat h (fun y ↦ f y*b y) x := by
    apply (integral_pos_iff_support_of_nonneg (fun z ↦ (hbpos z).le) hib).mpr
    have he : Function.support (fun z ↦ f (x+Real.sqrt h*z)*b (x+Real.sqrt h*z))=univ :=
      eq_univ_of_forall (fun z ↦ (hbpos z).ne')
    rw [he,measure_univ]
    norm_num
  have hsplit : heat h f'' x=heat h (fun y ↦ f y*(a y)^2) x+heat h (fun y ↦ f y*b y) x := by
    change (∫ z,f (x+Real.sqrt h*z)*((a (x+Real.sqrt h*z))^2+b (x+Real.sqrt h*z)) ∂standardGaussian)=_
    simp_rw [mul_add]
    exact integral_add hia2 hib
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ.lipschitz hc.le y (Real.sqrt h)).ne'
  have heq : coleHopf c h ψ=fun y ↦ Real.log (heat h f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  rw [heq,heat_log_spatial_second hfd hf'd (hfc.mul ((hac.pow 2).add hbc)) hfg hag hf''g c h hp x]
  apply div_pos _ hc
  apply div_pos _ (sq_pos_of_pos hZ)
  rw [hsplit]
  change 0≤heat h f x*heat h (fun y ↦ f y*(a y)^2) x-(heat h f' x)^2 at hvar
  nlinarith [mul_pos hZ hKpos]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Controls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def controlAccum {Ω : Type*} (γ : ℝ → ℝ)
    (α : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, γ s*(α (Real.toNNReal s) ω)^n

end SKValue

namespace SKValue

noncomputable def controlState {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (γ : ℝ → ℝ) (α : ℝ≥0 → Ω → ℝ) (x t : ℝ) (ω : Ω) : ℝ :=
  x+B (Real.toNNReal t) ω+controlAccum γ α 1 t ω

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ValueStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

structure ValueStrip (T : ℝ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ) (K L : ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0 : ℝ) T)
  smooth : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 3 (V t)
  bounded : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (V t) x|≤1
  second_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (deriv (V t)) x|≤K
  third_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |iteratedDeriv 3 (V t) x|≤K
  product_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |(1/2 : ℝ)*(deriv (V t) x)^2|≤K
  second_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ x, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) x) volume 0 T
  product_integrable : ∀ x, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) x)^2)) volume 0 T
  pde : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
    V s x-V t x = -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))

noncomputable def valueMeshEnergy (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  ∑ i ∈ Finset.range j, (stepSize T N/2)*γ (meshTime T N i)*
    (deriv (V (meshTime T N i)) (euler T N γ (fun t ↦ deriv (V t)) z i))^2

noncomputable def valueMeshCompensated (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  V (meshTime T N j) (euler T N γ (fun t ↦ deriv (V t)) z j)-valueMeshEnergy T N γ V j z

noncomputable def valueMeshError (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z, (valueMeshCompensated T N γ V N z-V 0 0-∑ i : Fin N,
    Real.sqrt (stepSize T N)*deriv (V (meshTime T N i))
      (euler T N γ (fun t ↦ deriv (V t)) z i)*coordinate N i z)^2
    ∂gaussianProduct (Fin (N+1))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_BrownianCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

noncomputable def brownianCoordinates {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) (j : Fin n) : ℝ :=
  (B (((j : ℕ) + 1 : ℕ) * δ) ω - B ((j : ℕ) * δ) ω) / Real.sqrt δ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ShiftedBrownianCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators

noncomputable def shiftedBrownianCoordinates {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ≥0) (T : ℝ) (N : ℕ) (i : Fin N) (ω : Ω) : ℝ :=
  brownianCoordinates (fun r ω ↦ B (a+r) ω-B a ω) (Real.toNNReal (stepSize T N)) N ω i

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShiftedPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
namespace SKValue

def shiftedPairing {N : ℕ} (A B : Fin (N+1) → ℝ) (bstar : ℝ) : ℝ :=
  (∑ i : Fin N, A i.castSucc*B i.succ)+A (Fin.last N)*bstar

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_CoupledCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

noncomputable def coupledCoordinates {Ω : Type*} (T : ℝ) (N : ℕ) (B : ℝ≥0 → Ω → ℝ) :
    Ω → Fin (N+1) → ℝ := brownianCoordinates B (Real.toNNReal (T/N)) (N+1)

noncomputable def coupledEuler {Ω : Type*} (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (N j : ℕ) (ω : Ω) : ℝ :=
  if N=0 then 0 else euler T N γ u (coupledCoordinates T N B ω) j

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_RawIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

noncomputable def rawIncrement {N : ℕ} (H : (Fin (N+1) → ℝ) → ℝ) (j : ℕ) :
    (Fin (N+1) → ℝ) → ℝ := fun z ↦ H z * coordinate N j z

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Feedback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def meshControl {Ω : Type*} (T : ℝ) (N : ℕ) (H : Fin N → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j : Fin N, if meshTime T N j < t ∧ (t : ℝ)  ≤  meshTime T N (j+1) then H j ω else 0

noncomputable def feedbackControl {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (γ : ℝ → ℝ)
    (V : ℝ → ℝ → ℝ) (T : ℝ) (N : ℕ) : ℝ≥0 → Ω → ℝ :=
  meshControl T N (fun j ω ↦ deriv (V (meshTime T N j))
    (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

structure SmoothEvolution (T : ℝ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ) : Prop where
  slices : ∀ t∈Icc (0 : ℝ) T, SmoothTerminal (V t)
  continuous_value : ∀ x, ContinuousOn (fun t ↦ V t x) (Icc (0 : ℝ) T)
  continuous_jet : ∀ n x, ContinuousOn (fun t ↦ iteratedDeriv n (deriv (V t)) x) (Icc (0 : ℝ) T)
  bound : ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0 : ℝ) T, ∀ x,
    |iteratedDeriv n (deriv (V t)) x|≤C
  temporal : ∀ n, ∃ L : ℝ, 0≤L ∧ ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x,
    |iteratedDeriv n (deriv (V s)) x-iteratedDeriv n (deriv (V t)) x|≤L* |s-t|
  value_pde : ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x,
    V s x-V t x=-(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))
  gradient_pde : ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x,
    deriv (V s) x-deriv (V t) x=-(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (V r))) x+
      γ r*(deriv (V r) x*deriv (deriv (V r)) x))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TimePatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def patchTime {E : Type*} (a : ℝ) (f g : ℝ → E) (t : ℝ) : E :=
  if t≤a then f t else g (t-a)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_FiniteStepEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

abbrev HeatProfile := List (ℝ≥0 × ℝ≥0)

noncomputable def profileTime : HeatProfile → ℝ
  | [] => 0
  | p::l => (p.1 : ℝ)+profileTime l

noncomputable def profileCoeff : HeatProfile → ℝ → ℝ
  | [] => fun _ ↦ 0
  | p::l => patchTime (p.1 : ℝ) (fun _ ↦ (p.2 : ℝ)) (profileCoeff l)

noncomputable def profileValue (ψ : ℝ → ℝ) : HeatProfile → ℝ → ℝ → ℝ
  | [] => fun _ ↦ ψ
  | p::l => patchTime (p.1 : ℝ)
    (fun t ↦ coleHopf (p.2 : ℝ) ((p.1 : ℝ)-t) (profileValue ψ l 0)) (profileValue ψ l)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_EvenEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma gaussian_integral_neg (f : ℝ → ℝ) :
    (∫ z, f (-z) ∂standardGaussian)=∫ z, f z ∂standardGaussian := by
  have he := integral_map_equiv (μ := standardGaussian) (MeasurableEquiv.neg ℝ) f
  have hm : standardGaussian.map (MeasurableEquiv.neg ℝ)=standardGaussian := by
    change (gaussianReal 0 1).map (fun x ↦ -x)=gaussianReal 0 1
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  rw [hm] at he
  exact he.symm

lemma heat_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x) (h x : ℝ) :
    heat h ψ (-x)=heat h ψ x := by
  unfold heat
  rw [←gaussian_integral_neg (fun z ↦ ψ (-x+Real.sqrt h*z))]
  apply integral_congr_ae
  filter_upwards [] with z
  convert! hψ (x+Real.sqrt h*z) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma coleHopf_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x) (c h x : ℝ) :
    coleHopf c h ψ (-x)=coleHopf c h ψ x := by
  unfold coleHopf
  split_ifs
  · exact heat_even hψ h x
  · rw [heat_even (fun x ↦ by rw [hψ x])]

lemma deriv_even_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x)=f x) : deriv f 0=0 := by
  have he : (fun x ↦ f (-x))=f := funext hf
  have hd := deriv_comp_neg f (0 : ℝ)
  rw [he,neg_zero] at hd
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BackwardPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SKValue

structure BackwardBurgers where
  jet : ℕ → ℝ → ℝ → ℝ
  continuous : ∀ n, Continuous (fun p : ℝ×ℝ ↦ jet n p.1 p.2)
  bound : ∀ n, ∃ C : ℝ,0≤C ∧ ∀ t x,|jet n t x|≤C
  space : ∀ n t x, HasDerivAt (jet n t) (jet (n+1) t x) x
  time0 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 0 s x)
    ((1/2:ℝ)*jet 2 t x+jet 0 t x*jet 1 t x) t
  time1 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 1 s x)
    ((1/2:ℝ)*jet 3 t x+(jet 1 t x)^2+jet 0 t x*jet 2 t x) t
  time2 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 2 s x)
    ((1/2:ℝ)*jet 4 t x+3*jet 1 t x*jet 2 t x+jet 0 t x*jet 3 t x) t
  time3 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 3 s x)
    ((1/2:ℝ)*jet 5 t x+3*(jet 2 t x)^2+4*jet 1 t x*jet 3 t x+jet 0 t x*jet 4 t x) t
  zero0 : ∀ t, jet 0 t 0=0
  zero2 : ∀ t, jet 2 t 0=0
  positive : ∀ t x,0<x → 0<jet 0 t x
  slope_nonneg : ∀ t x,0≤jet 1 t x

lemma even_third_deriv_zero {f : ℝ → ℝ} (hf : ∀ x,f (-x)=f x) :
    iteratedDeriv 2 (deriv f) 0=0 := by
  have h := iteratedDeriv_comp_neg 3 f (0:ℝ)
  have he : (fun x ↦ f (-x))=f := funext hf
  rw [he] at h
  norm_num only [neg_zero,smul_eq_mul] at h
  have hz : iteratedDeriv 3 f 0=0 := by linarith
  simpa only [iteratedDeriv_succ'] using hz

noncomputable def SmoothTerminal.backwardBurgers {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (heven : ∀ x,ψ (-x)=ψ x) (hcurv : ∀ x,0<deriv (deriv ψ) x)
    {c : ℝ} (hc : 0 < c) : BackwardBurgers where
  jet := scaledHeatJet c ψ
  continuous := scaledHeatJet_continuous hψ hc.le
  bound := scaledHeatJet_bound hψ hc
  space := scaledHeatJet_space hψ hc.le
  time0 := fun _ ht x ↦ scaledHeatJet_time0 hψ hc ht x
  time1 := fun _ ht x ↦ scaledHeatJet_time1 hψ hc ht x
  time2 := fun _ ht x ↦ scaledHeatJet_time2 hψ hc ht x
  time3 := fun _ ht x ↦ scaledHeatJet_time3 hψ hc ht x
  zero0 := by
    intro t
    simp only [scaledHeatJet,iteratedDeriv_zero,deriv_even_zero (coleHopf_even heven c t),mul_zero]
  zero2 := by
    intro t
    simp only [scaledHeatJet,even_third_deriv_zero (coleHopf_even heven c t),mul_zero]
  positive := by
    intro t x hx
    have hp := hψ.coleHopf_curvature_pos hcurv hc t
    have hm := strictMono_of_deriv_pos hp
    have hh := hm hx
    rw [deriv_even_zero (coleHopf_even heven c t)] at hh
    exact mul_pos hc hh
  slope_nonneg := by
    intro t x
    simpa only [scaledHeatJet,iteratedDeriv_one] using (mul_pos hc (hψ.coleHopf_curvature_pos hcurv hc t x)).le

namespace BackwardBurgers
variable (F : BackwardBurgers)

noncomputable def k (t x : ℝ) := F.jet 2 t x+2*F.jet 0 t x*F.jet 1 t x
noncomputable def kx (t x : ℝ) := F.jet 3 t x+2*(F.jet 1 t x)^2+2*F.jet 0 t x*F.jet 2 t x
noncomputable def kxx (t x : ℝ) := F.jet 4 t x+6*F.jet 1 t x*F.jet 2 t x+2*F.jet 0 t x*F.jet 3 t x
noncomputable def kt (t x : ℝ) := (1/2:ℝ)*F.kxx t x+F.jet 0 t x*F.kx t x+F.jet 1 t x*F.k t x
noncomputable def n (t x : ℝ) := F.jet 0 t x*F.jet 3 t x-F.jet 1 t x*F.jet 2 t x+2*(F.jet 0 t x)^2*F.jet 2 t x
noncomputable def nx (t x : ℝ) := F.jet 0 t x*F.jet 4 t x-(F.jet 2 t x)^2+
  4*F.jet 0 t x*F.jet 1 t x*F.jet 2 t x+2*(F.jet 0 t x)^2*F.jet 3 t x
noncomputable def nxx (t x : ℝ) := F.jet 0 t x*F.jet 5 t x+F.jet 1 t x*F.jet 4 t x-
  2*F.jet 2 t x*F.jet 3 t x+4*(F.jet 1 t x)^2*F.jet 2 t x+
  4*F.jet 0 t x*(F.jet 2 t x)^2+8*F.jet 0 t x*F.jet 1 t x*F.jet 3 t x+
  2*(F.jet 0 t x)^2*F.jet 4 t x
noncomputable def nt (t x : ℝ) := (1/2:ℝ)*F.nxx t x+
  (F.jet 0 t x-F.jet 1 t x/F.jet 0 t x)*F.nx t x+
  (F.k t x/F.jet 0 t x)*F.n t x+F.jet 0 t x*F.jet 2 t x*F.k t x

@[simp] lemma k_zero (t : ℝ) : F.k t 0=0 := by simp [k,F.zero2,F.zero0]
@[simp] lemma n_zero (t : ℝ) : F.n t 0=0 := by simp [n,F.zero2,F.zero0]

end BackwardBurgers
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ForwardComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

structure ForwardBurgers (T : ℝ) where
  jet : ℕ → ℝ → ℝ → ℝ
  continuous : ∀ n, Continuous (fun p : ℝ×ℝ ↦ jet n p.1 p.2)
  space : ∀ n t x, HasDerivAt (jet n t) (jet (n+1) t x) x
  time0 : ∀ t∈Ioc (0:ℝ) T, ∀ x, HasDerivAt (jet 0 · x)
    ((1/2:ℝ)*jet 2 t x-jet 0 t x*jet 1 t x) t
  time1 : ∀ t∈Ioc (0:ℝ) T, ∀ x, HasDerivAt (jet 1 · x)
    ((1/2:ℝ)*jet 3 t x-(jet 1 t x)^2-jet 0 t x*jet 2 t x) t
  time2 : ∀ t∈Ioc (0:ℝ) T, ∀ x, HasDerivAt (jet 2 · x)
    ((1/2:ℝ)*jet 4 t x-3*jet 1 t x*jet 2 t x-jet 0 t x*jet 3 t x) t
  bound : ∀ n, ∃ C:ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x, |jet (n+1) t x|≤C
  growth : ∃ C:ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x, |jet 0 t x|≤C*(1+|x|)
  zero0 : ∀ t, jet 0 t 0=0
  zero2 : ∀ t, jet 2 t 0=0

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogCoshTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def logCoshTerminal (M x : ℝ) : ℝ := Real.log (2*Real.cosh (M*x))/M

namespace JetExpr
noncomputable def fieldJet (σ : ℕ → JetExpr) (e : JetExpr) : ℕ → JetExpr
  | 0 => e
  | n+1 => D σ (fieldJet σ e n)

end JetExpr

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_CoupledComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue
namespace BackwardBurgers
variable {T : ℝ} (B : BackwardBurgers) (F : ForwardBurgers T) (b : ℝ)
noncomputable def ratioJ (t x : ℝ) : ℝ := B.jet 0 (b-t) x*F.jet 1 t x-F.jet 0 t x*B.jet 1 (b-t) x
noncomputable def ratioJx (t x : ℝ) : ℝ := B.jet 0 (b-t) x*F.jet 2 t x-F.jet 0 t x*B.jet 2 (b-t) x
noncomputable def ratioJxx (t x : ℝ) : ℝ := B.jet 1 (b-t) x*F.jet 2 t x+
  B.jet 0 (b-t) x*F.jet 3 t x-F.jet 1 t x*B.jet 2 (b-t) x-F.jet 0 t x*B.jet 3 (b-t) x
noncomputable def ratioJt (t x : ℝ) : ℝ := (1/2:ℝ)*B.ratioJxx F b t x-
  (B.jet 1 (b-t) x/B.jet 0 (b-t) x)*B.ratioJx F b t x-
  (B.jet 1 (b-t) x+F.jet 1 t x)*B.ratioJ F b t x+
  (F.jet 0 t x/B.jet 0 (b-t) x)*B.n (b-t) x-
  B.jet 0 (b-t) x*F.jet 0 t x*(B.jet 2 (b-t) x+F.jet 2 t x)

end BackwardBurgers
end SKValue

end

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

noncomputable def spatialJet (c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  c*iteratedDeriv n (deriv ψ) x
noncomputable def spatialK (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  spatialJet c ψ 2 x+2*spatialJet c ψ 0 x*spatialJet c ψ 1 x
noncomputable def spatialN (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  spatialJet c ψ 0 x*spatialJet c ψ 3 x-spatialJet c ψ 1 x*spatialJet c ψ 2 x+
    2*(spatialJet c ψ 0 x)^2*spatialJet c ψ 2 x

structure BackwardShape (c : ℝ) (ψ : ℝ → ℝ) : Prop where
  even : ∀ x,ψ (-x)=ψ x
  convex : ∀ x,0<deriv (deriv ψ) x
  w : ∀ x,0≤x → spatialJet c ψ 2 x≤0
  k : ∀ x,0≤x → spatialK c ψ x≤0
  n : ∀ x,0≤x → 0≤ spatialN c ψ x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ProfileShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue
lemma moving_partial_deriv {f ft fx : ℝ → ℝ → ℝ} {p q : ℝ → ℝ} {p' q' t : ℝ}
    (hdt : ∀ᶠ z : ℝ×ℝ in 𝓝 (p t,q t), HasDerivAt (f · z.2) (ft z.1 z.2) z.1)
    (hdx : ∀ᶠ z : ℝ×ℝ in 𝓝 (p t,q t), HasDerivAt (f z.1) (fx z.1 z.2) z.2)
    (hct : ContinuousAt (fun z : ℝ×ℝ ↦ ft z.1 z.2) (p t,q t))
    (hcx : ContinuousAt (fun z : ℝ×ℝ ↦ fx z.1 z.2) (p t,q t))
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s ↦ f (p s) (q s)) (ft (p t) (q t)*p'+fx (p t) (q t)*q') t := by
  have hd := hasStrictFDerivAt_uncurry_coprod
    (f₁ := fun a b ↦ ContinuousLinearMap.toSpanSingleton ℝ (ft a b))
    (f₂ := fun a b ↦ ContinuousLinearMap.toSpanSingleton ℝ (fx a b))
    (hdt.mono (fun z hz ↦ hz.hasFDerivAt))
    (hdx.mono (fun z hz ↦ hz.hasFDerivAt))
    (ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp hct)
    (ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp hcx)
  convert! hd.hasFDerivAt.comp_hasDerivAt t (hp.prodMk hq) using 1
  all_goals try with_reducible_and_instances rfl
  change ft (p t) (q t)*p'+fx (p t) (q t)*q'=p'*ft (p t) (q t)+q'*fx (p t) (q t)
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue
noncomputable def heatDen (a t : ℝ) : ℝ := a+max 0 t
noncomputable def heatScale (a t : ℝ) : ℝ := a/heatDen a t
noncomputable def heatTime (a t : ℝ) : ℝ := a-a^2/heatDen a t

lemma heatDen_pos {a : ℝ} (ha : 0<a) (t : ℝ) : 0<heatDen a t :=
  add_pos_of_pos_of_nonneg ha (le_max_left _ _)
lemma heatDen_of_nonneg (a : ℝ) {t : ℝ} (ht : 0≤t) : heatDen a t=a+t := by
  simp only [heatDen,max_eq_right ht]
lemma heatScale_mem {a : ℝ} (ha : 0<a) (t : ℝ) : heatScale a t∈Icc (0:ℝ) 1 := by
  constructor
  · exact (div_pos ha (heatDen_pos ha t)).le
  · exact (div_le_one (heatDen_pos ha t)).mpr (by dsimp [heatDen]; linarith [le_max_left (0:ℝ) t])
lemma heatTime_pos {a t : ℝ} (ha : 0<a) (ht : 0<t) : 0<heatTime a t := by
  dsimp [heatTime]
  rw [heatDen_of_nonneg a ht.le]
  rw [sub_pos,div_lt_iff₀ (add_pos ha ht)]
  nlinarith
lemma heatDen_continuous (a : ℝ) : Continuous (heatDen a) := continuous_const.add (continuous_const.max continuous_id)
lemma heatScale_continuous {a : ℝ} (ha : 0<a) : Continuous (heatScale a) :=
  continuous_const.div (heatDen_continuous a) (fun t ↦ (heatDen_pos ha t).ne')
lemma heatTime_continuous {a : ℝ} (ha : 0<a) : Continuous (heatTime a) :=
  continuous_const.sub (continuous_const.div (heatDen_continuous a) (fun t ↦ (heatDen_pos ha t).ne'))
lemma heatDen_hasDerivAt {a t : ℝ} (ht : 0<t) : HasDerivAt (heatDen a) 1 t := by
  apply ((hasDerivAt_id t).const_add a).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact heatDen_of_nonneg a hs.le
lemma heatScale_hasDerivAt {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    HasDerivAt (heatScale a) (-heatScale a t/heatDen a t) t := by
  convert! (hasDerivAt_const t a).div (heatDen_hasDerivAt ht) (heatDen_pos ha t).ne' using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [heatScale]; field_simp; ring
lemma heatTime_hasDerivAt {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    HasDerivAt (heatTime a) ((heatScale a t)^2) t := by
  convert! (hasDerivAt_const t a).sub
    ((hasDerivAt_const t (a^2)).div (heatDen_hasDerivAt ht) (heatDen_pos ha t).ne') using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [heatScale]; field_simp; ring

lemma scaledHeatJet_moving {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c a t : ℝ}
    (hc : 0 < c) (ha : 0<a) (ht : 0<t) (n : ℕ) (x : ℝ)
    (F : ℝ → ℝ → ℝ) (hF : Continuous (fun p : ℝ×ℝ ↦ F p.1 p.2))
    (hft : ∀ s,0 < s → ∀ y,HasDerivAt (scaledHeatJet c ψ n · y) (F s y) s) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ n (heatTime a s) (heatScale a s*x))
      (F (heatTime a t) (heatScale a t*x)*(heatScale a t)^2-
        scaledHeatJet c ψ (n+1) (heatTime a t) (heatScale a t*x)*heatScale a t/heatDen a t*x) t := by
  have hp := heatTime_hasDerivAt ha ht
  have hq := (heatScale_hasDerivAt ha ht).mul_const x
  have hh := moving_partial_deriv
    (f := scaledHeatJet c ψ n) (ft := F) (fx := scaledHeatJet c ψ (n+1))
    (p := heatTime a) (q := fun s ↦ heatScale a s*x)
    (by
      filter_upwards [(continuous_fst.tendsto (heatTime a t,heatScale a t*x)).eventually
        (Ioi_mem_nhds (heatTime_pos ha ht))] with z hz
      exact hft z.1 hz z.2)
    (Filter.Eventually.of_forall (fun z ↦ scaledHeatJet_space hψ hc.le n z.1 z.2))
    hF.continuousAt (scaledHeatJet_continuous hψ hc.le (n+1)).continuousAt hp hq
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

noncomputable def forwardJet (a c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  (if n=0 then x/heatDen a t else if n=1 then 1/heatDen a t else 0)-
    (heatScale a t)^(n+1)*scaledHeatJet c ψ n (heatTime a t) (heatScale a t*x)
lemma forwardJet_zero (a c : ℝ) (ψ : ℝ → ℝ) (t x : ℝ) :
    forwardJet a c ψ 0 t x=x/heatDen a t-
      heatScale a t*scaledHeatJet c ψ 0 (heatTime a t) (heatScale a t*x) := by simp [forwardJet]
lemma forwardJet_succ_succ (a c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) :
    forwardJet a c ψ (n+2) t x= -(heatScale a t)^(n+3)*scaledHeatJet c ψ (n+2) (heatTime a t) (heatScale a t*x) := by
  simp [forwardJet,Nat.add_assoc,neg_mul]
lemma forwardJet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (ha : 0<a) (hc : 0 ≤ c) (n : ℕ) : Continuous (fun p : ℝ×ℝ ↦ forwardJet a c ψ n p.1 p.2) := by
  have h1 : Continuous (fun p : ℝ×ℝ ↦ heatDen a p.1) := (heatDen_continuous a).comp continuous_fst
  have h2 : Continuous (fun p : ℝ×ℝ ↦ heatScale a p.1) := (heatScale_continuous ha).comp continuous_fst
  have h3 : Continuous (fun p : ℝ×ℝ ↦ heatTime a p.1) := (heatTime_continuous ha).comp continuous_fst
  have h4 := (scaledHeatJet_continuous hψ hc n).comp (h3.prodMk (h2.mul continuous_snd))
  dsimp only [forwardJet]
  split_ifs <;> fun_prop (disch := intro p; exact (heatDen_pos ha p.1).ne')
lemma forwardJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (hc : 0 ≤ c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (forwardJet a c ψ n t) (forwardJet a c ψ (n+1) t x) x := by
  have hd := ((scaledHeatJet_space hψ hc n (heatTime a t) (heatScale a t*x)).comp x
    ((hasDerivAt_id x).const_mul (heatScale a t))).const_mul ((heatScale a t)^(n+1))
  obtain rfl | n := n
  · convert! ((hasDerivAt_id x).div_const (heatDen a t)).sub hd using 1
    all_goals try with_reducible_and_instances rfl
    simp [forwardJet]
    ring
  obtain rfl | n := n
  · convert! (hasDerivAt_const x (1/heatDen a t)).sub hd using 1
    all_goals try with_reducible_and_instances rfl
    simp [forwardJet]
    ring
  · convert! hd.neg using 1
    · funext y; simp [forwardJet,pow_succ]
    · simp [forwardJet,pow_succ]; ring
end SKValue

end

section

open Set Filter
open scoped Topology
namespace SKValue
lemma abs_sub_upper (x y : ℝ) : |x-y|≤|x|+|y| := by
  simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le x 0 y
lemma heatDen_inv_hasDerivAt {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    HasDerivAt (fun s ↦ 1/heatDen a s) (-(1/heatDen a t)^2) t := by
  convert! (heatDen_hasDerivAt ht).inv (heatDen_pos ha t).ne' using 1
  · funext s; simp only [one_div,Pi.inv_apply]
  · simp only [one_div,inv_pow]; ring

lemma forwardJet_time0 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c t : ℝ}
    (ha : 0<a) (hc : 0 < c) (ht : 0<t) (x : ℝ) :
    HasDerivAt (forwardJet a c ψ 0 · x)
      ((1/2:ℝ)*forwardJet a c ψ 2 t x-forwardJet a c ψ 0 t x*forwardJet a c ψ 1 t x) t := by
  have hm := scaledHeatJet_moving hψ hc ha ht 0 x
    (fun s y ↦ (1/2:ℝ)*scaledHeatJet c ψ 2 s y+scaledHeatJet c ψ 0 s y*scaledHeatJet c ψ 1 s y)
    (by
      have h0 := scaledHeatJet_continuous hψ hc.le 0
      have h1 := scaledHeatJet_continuous hψ hc.le 1
      have h2 := scaledHeatJet_continuous hψ hc.le 2
      have h3 := scaledHeatJet_continuous hψ hc.le 3
      have h4 := scaledHeatJet_continuous hψ hc.le 4
      fun_prop)
    (fun s hs y ↦ scaledHeatJet_time0 hψ hc hs y)
  have hl := heatScale_hasDerivAt ha ht
  have hh := ((heatDen_inv_hasDerivAt ha ht).const_mul x).sub (hl.mul hm)
  convert! hh using 1
  · funext s; simp [forwardJet,div_eq_mul_inv]
  · simp only [forwardJet,ite_true,ite_false,show (1:ℕ)≠0 by omega,
      show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega]
    norm_num
    simp only [div_eq_mul_inv]
    ring

lemma forwardJet_time1 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c t : ℝ}
    (ha : 0<a) (hc : 0 < c) (ht : 0<t) (x : ℝ) :
    HasDerivAt (forwardJet a c ψ 1 · x)
      ((1/2:ℝ)*forwardJet a c ψ 3 t x-(forwardJet a c ψ 1 t x)^2-forwardJet a c ψ 0 t x*forwardJet a c ψ 2 t x) t := by
  have hm := scaledHeatJet_moving hψ hc ha ht 1 x
    (fun s y ↦ (1/2:ℝ)*scaledHeatJet c ψ 3 s y+(scaledHeatJet c ψ 1 s y)^2+scaledHeatJet c ψ 0 s y*scaledHeatJet c ψ 2 s y)
    (by
      have h0 := scaledHeatJet_continuous hψ hc.le 0
      have h1 := scaledHeatJet_continuous hψ hc.le 1
      have h2 := scaledHeatJet_continuous hψ hc.le 2
      have h3 := scaledHeatJet_continuous hψ hc.le 3
      have h4 := scaledHeatJet_continuous hψ hc.le 4
      fun_prop)
    (fun s hs y ↦ scaledHeatJet_time1 hψ hc hs y)
  have hl := heatScale_hasDerivAt ha ht
  have hh := (heatDen_inv_hasDerivAt ha ht).sub ((hl.pow 2).mul hm)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp [forwardJet,div_eq_mul_inv]
  ring

lemma forwardJet_time2 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c t : ℝ}
    (ha : 0<a) (hc : 0 < c) (ht : 0<t) (x : ℝ) :
    HasDerivAt (forwardJet a c ψ 2 · x)
      ((1/2:ℝ)*forwardJet a c ψ 4 t x-3*forwardJet a c ψ 1 t x*forwardJet a c ψ 2 t x-forwardJet a c ψ 0 t x*forwardJet a c ψ 3 t x) t := by
  have hm := scaledHeatJet_moving hψ hc ha ht 2 x
    (fun s y ↦ (1/2:ℝ)*scaledHeatJet c ψ 4 s y+3*scaledHeatJet c ψ 1 s y*scaledHeatJet c ψ 2 s y+scaledHeatJet c ψ 0 s y*scaledHeatJet c ψ 3 s y)
    (by
      have h0 := scaledHeatJet_continuous hψ hc.le 0
      have h1 := scaledHeatJet_continuous hψ hc.le 1
      have h2 := scaledHeatJet_continuous hψ hc.le 2
      have h3 := scaledHeatJet_continuous hψ hc.le 3
      have h4 := scaledHeatJet_continuous hψ hc.le 4
      fun_prop)
    (fun s hs y ↦ scaledHeatJet_time2 hψ hc hs y)
  have hl := heatScale_hasDerivAt ha ht
  have hh := ((hl.pow 3).mul hm).neg
  convert! hh using 1
  · funext s; simp [forwardJet]
  · simp only [forwardJet,ite_true,ite_false,show (1:ℕ)≠0 by omega,
      show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega,
      show (3:ℕ)≠0 by omega,show (3:ℕ)≠1 by omega,
      show (4:ℕ)≠0 by omega,show (4:ℕ)≠1 by omega]
    norm_num
    simp only [div_eq_mul_inv]
    ring
lemma heatDen_inv_bound {a : ℝ} (ha : 0<a) (t : ℝ) :
    0≤1/heatDen a t ∧ 1/heatDen a t≤1/a := by
  refine ⟨one_div_nonneg.mpr (heatDen_pos ha t).le,?_⟩
  exact one_div_le_one_div_of_le ha (by dsimp [heatDen]; linarith [le_max_left (0:ℝ) t])

lemma forwardJet_bound {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (ha : 0<a) (hc : 0 < c) (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|forwardJet a c ψ (n+1) t x|≤C := by
  obtain ⟨C,hC,hb⟩ := scaledHeatJet_bound hψ hc (n+1)
  refine ⟨1/a+C,by positivity,?_⟩
  intro t x
  have hs := heatScale_mem ha t
  have hh : |(heatScale a t)^(n+1+1)*scaledHeatJet c ψ (n+1) (heatTime a t) (heatScale a t*x)|≤C := by
    rw [abs_mul,abs_pow,abs_of_nonneg hs.1]
    calc
      _ ≤ 1*C := mul_le_mul (pow_le_one₀ hs.1 hs.2) (hb _ _) (abs_nonneg _) (by norm_num)
      _ = C := one_mul _
  have hi := heatDen_inv_bound ha t
  calc
    _ ≤ |if n+1=0 then x/heatDen a t else if n+1=1 then 1/heatDen a t else 0|+C :=
      (abs_sub_upper _ _).trans (add_le_add le_rfl hh)
    _ ≤ 1/a+C := by
      simp only [Nat.add_one_ne_zero,ite_false]
      split_ifs <;> simp only [abs_of_nonneg hi.1,abs_zero] <;> linarith [one_div_nonneg.mpr ha.le]

lemma forwardJet_growth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (ha : 0<a) (hc : 0 < c) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|forwardJet a c ψ 0 t x|≤C*(1+|x|) := by
  obtain ⟨C,hC,hb⟩ := scaledHeatJet_bound hψ hc 0
  refine ⟨1/a+C,by positivity,?_⟩
  intro t x
  have hs := heatScale_mem ha t
  have hi := heatDen_inv_bound ha t
  have hh : |heatScale a t*scaledHeatJet c ψ 0 (heatTime a t) (heatScale a t*x)|≤C := by
    rw [abs_mul,abs_of_nonneg hs.1]
    calc
      _ ≤ 1*C := mul_le_mul hs.2 (hb _ _) (abs_nonneg _) (by norm_num)
      _ = C := one_mul _
  rw [forwardJet_zero]
  calc
    _ ≤ |x/heatDen a t|+C := (abs_sub_upper _ _).trans (add_le_add le_rfl hh)
    _ = |x| *(1/heatDen a t)+C := by rw [abs_div,abs_of_pos (heatDen_pos ha t)]; ring
    _ ≤ |x| *(1/a)+C := add_le_add (mul_le_mul_of_nonneg_left hi.2 (abs_nonneg x)) le_rfl
    _ ≤ (1/a+C)*(1+|x|) := by nlinarith [mul_nonneg hC (abs_nonneg x),one_div_nonneg.mpr ha.le]

noncomputable def SmoothTerminal.forwardBurgers {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (heven : ∀ x,ψ (-x)=ψ x) {a c : ℝ} (ha : 0<a) (hc : 0 < c) (T : ℝ) : ForwardBurgers T where
  jet := forwardJet a c ψ
  continuous := forwardJet_continuous hψ ha hc.le
  space := forwardJet_space hψ hc.le
  time0 := fun _ ht x ↦ forwardJet_time0 hψ ha hc ht.1 x
  time1 := fun _ ht x ↦ forwardJet_time1 hψ ha hc ht.1 x
  time2 := fun _ ht x ↦ forwardJet_time2 hψ ha hc ht.1 x
  bound := by
    intro n
    obtain ⟨C,hC,hb⟩ := forwardJet_bound hψ ha hc n
    exact ⟨C,hC,fun t ht x ↦ hb t x⟩
  growth := by
    obtain ⟨C,hC,hb⟩ := forwardJet_growth hψ ha hc
    exact ⟨C,hC,fun t ht x ↦ hb t x⟩
  zero0 := by
    intro t
    simp only [forwardJet_zero,mul_zero,zero_div,scaledHeatJet,iteratedDeriv_zero,
      deriv_even_zero (coleHopf_even heven c _),sub_zero]
  zero2 := by
    intro t
    simp only [forwardJet_succ_succ,mul_zero,scaledHeatJet,
      even_third_deriv_zero (coleHopf_even heven c _)]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TerminalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

lemma BoundedSmooth.comp_mul {f : ℝ → ℝ} (hf : BoundedSmooth f) (a : ℝ) :
    BoundedSmooth (fun x ↦ f (a*x)) := by
  refine ⟨hf.smooth.comp (contDiff_const.mul contDiff_id),?_⟩
  intro n
  obtain ⟨C,hC,hb⟩ := hf.bound n
  refine ⟨|a|^n*C,by positivity,?_⟩
  intro x
  rw [iteratedDeriv_comp_const_mul (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))]
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (hb _) (by positivity)

lemma SmoothTerminal.deriv_abs_le {f : ℝ → ℝ} (hf : SmoothTerminal f) (x : ℝ) :
    |deriv f x|≤1 := by
  simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hf.lipschitz (x₀ := x)

lemma SmoothTerminal.linear {f g : ℝ → ℝ} (hf : SmoothTerminal f) (hg : SmoothTerminal g)
    {a b : ℝ} (hab : |a|+|b|≤1) : SmoothTerminal (fun x ↦ a*f x+b*g x) := by
  have hfd := hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hgd := hg.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hd : deriv (fun x ↦ a*f x+b*g x)=fun x ↦ a*deriv f x+b*deriv g x :=
    funext (fun x ↦ (((hfd x).hasDerivAt.const_mul a).add ((hgd x).hasDerivAt.const_mul b)).deriv)
  have hs : ContDiff ℝ ∞ (fun x ↦ a*f x+b*g x) := (contDiff_const.mul hf.smooth).add (contDiff_const.mul hg.smooth)
  refine ⟨?_,hs,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne')
    intro x
    have hh : |a*deriv f x+b*deriv g x|≤1 := calc
      _ ≤ |a*deriv f x|+|b*deriv g x| := abs_add_le _ _
      _ = |a| *|deriv f x|+|b| *|deriv g x| := by simp only [abs_mul]
      _ ≤ |a| *1+|b| *1 := add_le_add
        (mul_le_mul_of_nonneg_left (hf.deriv_abs_le x) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hg.deriv_abs_le x) (abs_nonneg b))
      _ ≤ 1 := by simpa only [mul_one] using hab
    rw [hd]
    exact_mod_cast hh
  · rw [hd]
    exact (hf.jets.const_mul a).add (hg.jets.const_mul b)

lemma SmoothTerminal.comp_mul {f : ℝ → ℝ} (hf : SmoothTerminal f) {a : ℝ}
    (ha : |a|≤1) : SmoothTerminal (fun x ↦ f (a*x)) := by
  have hfd := hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hd : deriv (fun x ↦ f (a*x))=fun x ↦ a*deriv f (a*x) := by
    funext x
    convert! ((hfd (a*x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul a)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
    ring
  have hs : ContDiff ℝ ∞ (fun x ↦ f (a*x)) := hf.smooth.comp (contDiff_const.mul contDiff_id)
  refine ⟨?_,hs,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne')
    intro x
    have hh : |a*deriv f (a*x)|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf.deriv_abs_le _) (abs_nonneg a)).trans (by simpa only [mul_one] using ha)
    rw [hd]
    exact_mod_cast hh
  · rw [hd]
    exact (hf.jets.comp_mul a).const_mul a

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ForwardDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
structure ForwardDensityData where
  variance : ℝ
  variance_pos : 0<variance
  size : ℝ
  size_pos : 0 < size
  potential : ℝ → ℝ
  smooth : SmoothTerminal potential
  even : ∀ x,potential (-x)=potential x

namespace ForwardDensityData
variable (D : ForwardDensityData)
noncomputable def weight (x : ℝ) : ℝ :=
  gaussianPDFReal 0 D.variance.toNNReal x*Real.exp (D.size*D.potential x)
noncomputable def jet (n : ℕ) (x : ℝ) : ℝ :=
  (if n=0 then x/D.variance else if n=1 then 1/D.variance else 0)-
    D.size*iteratedDeriv n (deriv D.potential) x

noncomputable def evolve (t : ℝ) (ht : 0≤t) : ForwardDensityData where
  variance := D.variance+t
  variance_pos := add_pos_of_pos_of_nonneg D.variance_pos ht
  size := D.size
  size_pos := D.size_pos
  potential := fun x ↦ coleHopf D.size (heatTime D.variance t) D.potential (heatScale D.variance t*x)
  smooth := (D.smooth.evolve D.size_pos.le _).comp_mul (by
    rw [abs_of_nonneg (heatScale_mem D.variance_pos t).1]
    exact (heatScale_mem D.variance_pos t).2)
  even := by
    intro x
    rw [mul_neg,coleHopf_even D.even]

end ForwardDensityData
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_DensityJump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace SKValue
lemma SmoothTerminal.const (c : ℝ) : SmoothTerminal (fun _ : ℝ ↦ c) := by
  refine ⟨?_,contDiff_const,?_⟩
  · exact (LipschitzWith.const c).weaken (by norm_num)
  · have he : deriv (fun _ : ℝ ↦ c)=(fun _ ↦ 0) := funext (fun x ↦ deriv_const x c)
    rw [he]
    exact BoundedSmooth.const 0
namespace ForwardDensityData
noncomputable def gaussian (a : ℝ) (ha : 0<a) : ForwardDensityData where
  variance := a
  variance_pos := ha
  size := 1
  size_pos := by norm_num
  potential := fun _ ↦ 0
  smooth := SmoothTerminal.const 0
  even := fun _ ↦ rfl

variable (D : ForwardDensityData) {φ : ℝ → ℝ}
noncomputable def jump (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ) : ForwardDensityData where
  variance := D.variance
  variance_pos := D.variance_pos
  size := D.size+δ
  size_pos := add_pos_of_pos_of_nonneg D.size_pos hδ
  potential := fun x ↦ (D.size/(D.size+δ))*D.potential x+(-δ/(D.size+δ))*φ x
  smooth := D.smooth.linear hφ (by
    have hp : 0<D.size+δ := add_pos_of_pos_of_nonneg D.size_pos hδ
    rw [abs_of_nonneg (div_nonneg D.size_pos.le hp.le),
      abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) hp.le)]
    field_simp
    linarith)
  even := by intro x; rw [D.even,heven]

end ForwardDensityData
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_Coercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SKValue.Certificate
noncomputable def Q (R K v b : ℝ) : ℝ :=
  (1/13)*v*b+(53/24)*v^2+(19/16)*K*v-2*(19/16)*R*b+(73/48)*R*v
noncomputable def T (R v j : ℝ) : ℝ := (2331/10000)*R*v+(87/2500)*j*v
noncomputable def F₂ (R K v b j : ℝ) : ℝ :=
  (4663/5000)*v^2*j+(6853/10000)*v^3-(1051/400)*K*v^2-(1073/500)*R*v^2-
  (b^2*(2*R*(19/16)-(1/13)*v)+
    b*(-2*K*(19/16)*v-R*(2331/10000)*v-2*R*(73/48)*v-2*(53/24)*v^2-(87/2500)*j*v))
noncomputable def W₂ (R K v b j z L : ℝ) : ℝ :=
  (2*R*v)*(-(1073/500)*v^2-2*(19/16)*b^2+b*((2331/10000)*v+2*(73/48)*v))+
  (2*v*K+R*j)*(-(1051/400)*v^2+2*(19/16)*b*v)+
  (-R*b)*(2*(4663/5000)*v*j+3*(6853/10000)*v^2-2*(1051/400)*K*v-
    2*(1073/500)*R*v+(1/13)*b^2+
    b*(2*K*(19/16)+R*(2331/10000)+2*R*(73/48)+4*(53/24)*v+(87/2500)*j))+
  (-z-b*v)*(-2*b*(2*R*(19/16)-(1/13)*v)+2*K*(19/16)*v+
    R*(2331/10000)*v+2*R*(73/48)*v+2*(53/24)*v^2+(87/2500)*j*v)+
  (-j*v+K*b-L)*((4663/5000)*v^2+(87/2500)*b*v)+(v+R-K)*F₂ R K v b j
noncomputable def remainder (R K v B j : ℝ) : ℝ :=
  (223/160000)*R^2*v^2+(4007/240000)*R^2*v*B+(1097/120000)*R^2*B^2+
  (83/80000)*R*K*v^2+(3343/24000)*R*K*v*B+(16259/23400000)*R*v^3+
  (30179/5460000)*R*v^2*B+(26/625)*R*v^2*j+(107/15000)*R*v*B^2+
  (3/2500)*R*v*B*j+(121/32500)*R*B^3+(11/10000)*R*B^2*j+
  (579/20000)*K^2*v^2+(207/2500)*K^2*v*B+(911/975000)*K*v^3+
  (349/420000)*K*v^2*B+(5011/5000)*K*v^2*j+(133/130000)*K*v*B^2+
  (87/2500)*K*v*B*j+(1661507/1521000000)*v^4+
  (633799/621075000)*v^3*B+(10657/1690000)*v^2*B^2

end SKValue.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_Cutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

noncomputable def OrderParameter.cutoff (γ : OrderParameter) (t : ℝ) : ℝ :=
  (Ico (0 : ℝ) 1).indicator γ.coeff t

noncomputable def limitedControl {Ω : Type*} (α : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  α (min (Real.toNNReal s) 1) ω

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

noncomputable def controlIntegral (γ : OrderParameter) (t : ℝ)
    {Ω : Type*} (α : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(1-t), γ.cutoff (t+s)*(limitedControl α s ω)^n

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def elapsedPayoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) (α : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_SupStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def elapsedValue {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (f : Filtration ℝ≥0 m) (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) : ℝ :=
  sSup {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α}

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def gridProfile (d : ℝ≥0) (f : ℕ → ℝ≥0) : ℕ → ℕ → HeatProfile
  | _,0 => []
  | j,n+1 => (d,f j)::gridProfile d f (j+1) n

noncomputable def gridDelta (n : ℕ) : ℝ≥0 := ⟨1/(n+1 : ℝ),by positivity⟩

noncomputable def OrderParameter.grid (γ : OrderParameter) (n : ℕ) : HeatProfile :=
  gridProfile (gridDelta n)
    (fun i ↦ (γ.coeff ((i : ℝ)/(n+1 : ℝ))).toNNReal) 0 (n+1)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def OrderParameter.gridError (γ : OrderParameter) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, |profileCoeff (γ.grid n) t-γ.cutoff t|

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def smoothApprox (γ : OrderParameter) (n : ℕ) : ℝ → ℝ → ℝ :=
  profileValue (logCoshTerminal (n+1 : ℝ)) (γ.grid n)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BetaBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set
open scoped Topology
namespace SKValue

noncomputable def sqrtKernel (a b s : ℝ) : ℝ := (Real.sqrt (s-a))⁻¹*(Real.sqrt (b-s))⁻¹
noncomputable def sqrtMajorant (a b s : ℝ) : ℝ :=
  (2/Real.sqrt (b-a))*((Real.sqrt (s-a))⁻¹+(Real.sqrt (b-s))⁻¹)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_WeightedCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set
namespace SKValue

noncomputable def weightedCap (a b : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  sSup ((fun p : ℝ×ℝ ↦ Real.sqrt (b-p.1)*|F p.1 p.2|) '' (Icc a b ×ˢ univ))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

structure BoundedSmoothFamily (T : ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  slices : ∀ t∈Icc (0 : ℝ) T, BoundedSmooth (F t)
  bound : ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0 : ℝ) T, ∀ x, |iteratedDeriv n (F t) x|≤C
  joint : ∀ n, ContinuousOn (fun p : ℝ×ℝ ↦ iteratedDeriv n (F p.1) p.2) (Icc (0 : ℝ) T ×ˢ univ)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_DuhamelJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def duhamel (a b : ℝ) (γ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in a..b, γ s*heat (s-a) (F s) x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShortStripClose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def lowerJetConstant (m : ℕ) (A : ℝ) : ℝ :=
  ∑ i∈Finset.range m, (m.choose (i+1) : ℝ)*A*A

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TerminalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

noncomputable def terminalError (γ : OrderParameter) (t : ℝ) : ℝ :=
  Real.sqrt (1-t)+(1/2 : ℝ)*(∫ s in t..1, γ.cutoff s)

@[simp] lemma terminalError_one (γ : OrderParameter) : terminalError γ 1=0 := by
  simp [terminalError]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_UnitMomentMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

structure UnitMomentMartingale (ℱ : Filtration ℝ m) (f : ℝ → Ω → ℝ) : Prop where
  measurable : ∀ t ∈ Ico (0 : ℝ) 1, StronglyMeasurable[ℱ t] (f t)
  bounded : ∀ t ∈ Ico (0 : ℝ) 1, ∀ ω, |f t ω| ≤ 1
  condExp : ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, s ≤ t →
    μ[f t | ℱ s] =ᵐ[μ] f s
  secondMoment : ∀ t ∈ Ico (0 : ℝ) 1, ∫ ω, (f t ω)^2 ∂μ = t

variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

noncomputable def terminalTime (n : ℕ) : ℝ := 1-1/(n+1)

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_RealFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable def BrownianSpace.realFiltration (W : BrownianSpace) :
    Filtration ℝ W.measurableSpace :=
  ⟨fun t ↦ W.filtration t.toNNReal, fun _ _ h ↦ W.filtration.mono (Real.toNNReal_mono h),
    fun t ↦ W.filtration.le t.toNNReal⟩

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshBrownian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

noncomputable def meshBrownian (T : ℝ) (N : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  ∑ j : Fin N, Real.sqrt (stepSize T N)*coordinate N j z

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_StripRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

def SourceStripRegularity (W : BrownianSpace) (γ : OrderParameter) : Prop :=
  ∀ T∈Ico (0 : ℝ) 1, ∃ Kv Lv K L D Lu La : ℝ,
    ValueStrip T γ.coeff (phi W γ) Kv Lv ∧
    GradientStrip T γ.coeff (gradient W γ) K L ∧
    0≤D ∧ 0≤Lu ∧ 0≤La ∧
    (∀ t∈Icc (0 : ℝ) T, ∀ x, |curvature W γ t x|≤D) ∧
    (∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|)) ∧
    (∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |curvature W γ s x-curvature W γ t y|≤La*(|s-t|+|x-y|))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def crossFeedback (V U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (deriv (U t) x+deriv (V t) x)/2

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ForcedGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue

structure ForcedTest (T:ℝ) (γ:ℝ → ℝ) (u V b p:ℝ → ℝ → ℝ) (K L:ℝ) : Prop where
  K_nonneg : 0 ≤ K
  L_nonneg : 0 ≤ L
  gamma_nonneg : ∀ t∈Icc (0:ℝ) T,0 ≤ γ t
  gamma_mono : MonotoneOn γ (Icc (0:ℝ) T)
  drift_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (u t)
  drift_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|u t x| ≤ 1
  smooth : ∀ t∈Icc (0:ℝ) T,ContDiff ℝ 3 (V t)
  bound : ∀ t∈Icc (0:ℝ) T,∀ x,|V t x| ≤ K
  first_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (V t) x| ≤ K
  second_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (deriv (V t)) x| ≤ K
  third_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|iteratedDeriv 3 (V t) x| ≤ K
  b_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (b t)
  p_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (p t)
  b_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|b t x| ≤ K
  p_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|p t x| ≤ K
  b_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |b s y-b t x| ≤ L*(|s-t|+|y-x|)
  p_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |p s y-p t x| ≤ L*(|s-t|+|y-x|)
  b_integrable : ∀ y,IntervalIntegrable (fun s ↦ b s y) volume 0 T
  p_integrable : ∀ y,IntervalIntegrable (fun s ↦ γ s*p s y) volume 0 T
  pde : ∀ a∈Icc (0:ℝ) T,∀ d∈Icc (0:ℝ) T,∀ x,
    V d x-V a x=∫ s in a..d,(1/2:ℝ)*b s x+γ s*p s x
noncomputable def forcedSource (γ:ℝ → ℝ) (u V b p:ℝ → ℝ → ℝ) (t x:ℝ) : ℝ :=
  (1/2:ℝ)*(b t x+deriv (deriv (V t)) x)+γ t*(p t x+u t x*deriv (V t) x)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_PolynomialObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
structure BoundedJoint (T:ℝ) (F:ℝ → ℝ → ℝ) : Prop where
  bounded : ∃ C:ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) T,∀ x,|F t x|≤C
  joint : ∃ L:ℝ,0≤L ∧ ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |F s y-F t x|≤L*(|s-t|+|y-x|)
namespace JetExpr
noncomputable def spatial (e:JetExpr):JetExpr := D (fun n ↦ coord (n+1)) e
noncomputable def spatialIter : ℕ → JetExpr → JetExpr
  | 0,e => e
  | n+1,e => spatial (spatialIter n e)
end JetExpr
noncomputable def polyJet (V:ℝ → ℝ → ℝ) (e:JetExpr) (t x:ℝ):ℝ :=
  e.eval (fun n ↦ iteratedDeriv n (deriv (V t)) x)
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def weightedFamilyIntegral (a b : ℝ) (γ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in a..b, γ s*F s x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HigherPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
namespace JetExpr
noncomputable def timeB (e:JetExpr):JetExpr := D (fun n ↦ mul (const (-1)) (coord (n+2))) e
noncomputable def timeP (e:JetExpr):JetExpr := D (fun n ↦ mul (const (-1)) ((mul (coord 0) (coord 1)).spatialIter n)) e
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CrossMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def crossMeshSource (T : ℝ) (N : ℕ) (γ β : ℝ → ℝ) (V U : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j∈Finset.range N,(stepSize T N/2)*(β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2
      ∂gaussianProduct (Fin (N+1)))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_PolynomialGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
namespace JetExpr
noncomputable def sourceA (e:JetExpr):JetExpr := mul (const (1/2)) (add e.timeB (e.spatialIter 2))
noncomputable def sourceP (e:JetExpr):JetExpr := add e.timeP (mul (coord 0) e.spatial)
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_CoupledDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology
namespace SKValue
structure ForwardShape (c:ℝ) (A:ℝ → ℝ) (D:ForwardDensityData) : Prop where
  slope : ∀ x,1/D.variance≤D.jet 1 x
  concave : ∀ x,0≤x → D.jet 2 x≤0
  coupled : ∀ x,0≤x → 0≤ spatialJet c A 0 x*D.jet 1 x-D.jet 0 x*spatialJet c A 1 x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_PolynomialMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
noncomputable def jetMoment (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ)
    (e:JetExpr) (t:ℝ):ℝ := ∫ z,polyJet (phi W γ) e t (X t z) ∂W.μ
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
namespace JetExpr
noncomputable def square (e:JetExpr):JetExpr := mul e e
noncomputable def cube (e:JetExpr):JetExpr := mul (mul e e) e
noncomputable def momentExpr : JetExpr := square (coord 0)
noncomputable def curvatureExpr : JetExpr := square (coord 1)
noncomputable def curvatureSlope (c:ℝ) : JetExpr := add (square (coord 2)) (mul (const (-2*c)) (cube (coord 1)))
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue
noncomputable def weightedJet (c : ℝ) (ψ f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n+1 => fun x ↦ deriv (weightedJet c ψ f n) x+weightedJet c ψ f n x*(c*deriv ψ x)

noncomputable def responseJet (c : ℝ) (ψ f : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv n (heat t (fun y ↦ Real.exp (c*ψ y)*f y)) x /
    heat t (fun y ↦ Real.exp (c*ψ y)) x
noncomputable def baseJet (c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  normalizedJet (fun t ↦ heat t (fun y ↦ Real.exp (c*ψ y))) n t x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ResponseJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
noncomputable def combinedJet (c:ℝ) (ψ f:ℝ → ℝ) (j:ℕ) (t x:ℝ) : ℝ :=
  if j%2=0 then baseJet c ψ (j/2) t x else responseJet c ψ f (j/2) t x
namespace JetExpr
noncomputable def responseσx (j:ℕ) : JetExpr :=
  add (coord (j+2)) (mul (const (-1)) (mul (coord j) (coord 2)))
noncomputable def responseσt (j:ℕ) : JetExpr :=
  mul (const (1/2)) (add (coord (j+4)) (mul (const (-1)) (mul (coord j) (coord 4))))
noncomputable def responseExpr : ℕ → JetExpr
  | 0 => coord 1
  | n+1 => D responseσx (responseExpr n)
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_StrictProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def liftProfile (ε : ℝ≥0) (k : ℕ) : HeatProfile → HeatProfile
  | [] => []
  | p::l => (p.1,p.2+ε*k)::liftProfile ε (k+1) l

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TestGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace SKValue
structure BackwardTest (T:ℝ) (γ:ℝ → ℝ) (u V:ℝ → ℝ → ℝ) (K L:ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t∈Icc (0:ℝ) T,0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0:ℝ) T)
  drift_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (u t)
  drift_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|u t x|≤1
  smooth : ∀ t∈Icc (0:ℝ) T,ContDiff ℝ 3 (V t)
  bound : ∀ t∈Icc (0:ℝ) T,∀ x,|V t x|≤K
  first_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (V t) x|≤K
  second_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (deriv (V t)) x|≤K
  third_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|iteratedDeriv 3 (V t) x|≤K
  second_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |u s y*deriv (V s) y-u t x*deriv (V t) x|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ y,IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume 0 T
  product_integrable : ∀ y,IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (V s) y)) volume 0 T
  pde : ∀ a∈Icc (0:ℝ) T,∀ b∈Icc (0:ℝ) T,∀ x,
    V b x-V a x=-(∫ s in a..b,(1/2:ℝ)*deriv (deriv (V s)) x+γ s*(u s x*deriv (V s) x))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

structure LinearEvolution (T:ℝ) (γ:ℝ → ℝ) (A V:ℝ → ℝ → ℝ) : Prop where
  slices : ∀ t∈Icc (0:ℝ) T,BoundedSmooth (V t)
  continuous_jet : ∀ n x,ContinuousOn (fun t ↦ iteratedDeriv n (V t) x) (Icc (0:ℝ) T)
  bound : ∀ n,∃ C:ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) T,∀ x,|iteratedDeriv n (V t) x|≤C
  temporal : ∀ n,∃ C:ℝ,0≤C ∧ ∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x,
    |iteratedDeriv n (V s) x-iteratedDeriv n (V t) x|≤C*|s-t|
  pde : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x,V s x-V t x=
    -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TestPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

noncomputable def profileResponse (ψ f:ℝ → ℝ) : HeatProfile → ℝ → ℝ → ℝ
  | [] => fun _ ↦ f
  | p::l => patchTime (p.1:ℝ)
    (fun t ↦ responseJet (p.2:ℝ) (profileValue ψ l 0) (profileResponse ψ f l 0) 0 ((p.1:ℝ)-t))
    (profileResponse ψ f l)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TruncatedStieltjes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma clamp_mem {T : ℝ} (hT : T∈Ico (0 : ℝ) 1) (t : ℝ) :
    min T (max 0 t)∈Ico (0 : ℝ) 1 :=
  ⟨le_min hT.1 (le_max_left _ _),(min_le_left _ _).trans_lt hT.2⟩

noncomputable def OrderParameter.truncatedStieltjes (γ : OrderParameter) (T : ℝ)
    (hT : T∈Ico (0 : ℝ) 1) : StieltjesFunction ℝ where
  toFun t := γ.coeff (min T (max 0 t))
  mono' a b hab := γ.monotone (clamp_mem hT a) (clamp_mem hT b)
    (min_le_min_left T (max_le_max_left 0 hab))
  right_continuous' t := by
    apply (γ.rightContinuous _ (clamp_mem hT t)).comp (f := fun s : ℝ ↦ min T (max 0 s))
      ((continuous_const.min (continuous_const.max continuous_id)).continuousWithinAt)
    intro u hu
    exact min_le_min_left T (max_le_max_left 0 hu)

noncomputable def OrderParameter.truncatedMass (γ : OrderParameter) (T : ℝ)
    (hT : T∈Ico (0 : ℝ) 1) : Measure ℝ :=
  (γ.truncatedStieltjes T hT).measure.restrict (Ioc 0 T)+
    ENNReal.ofReal (γ.coeff 0) • Measure.dirac 0

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_UniformPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
structure BoundedUniformLimit {A:Type*} (F:ℕ → A → ℝ) (f:A → ℝ) : Prop where
  tendsto : TendstoUniformly F f atTop
  bound : ∃ C:ℝ,0 ≤ C ∧ (∀ n x,|F n x| ≤ C) ∧ ∀ x,|f x| ≤ C
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ProfileSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue

noncomputable def splitLength (a b:ℝ) (hab:a≤b) (n:ℕ) : ℝ≥0 :=
  ⟨(b-a)/(n+1:ℝ),div_nonneg (sub_nonneg.mpr hab) (by positivity)⟩
noncomputable def OrderParameter.splitSegment (γ:OrderParameter) (a b:ℝ)
    (hab:a≤b) (n:ℕ) : HeatProfile :=
  gridProfile (splitLength a b hab n)
    (fun i ↦ (γ.coeff (a+(i:ℝ)*(splitLength a b hab n))).toNNReal+gridDelta n) 0 (n+1)

noncomputable def OrderParameter.splitGrid (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : HeatProfile :=
  γ.splitSegment 0 t t.property.1.le n++γ.splitSegment t 1 t.property.2.le n
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
noncomputable def OrderParameter.splitError (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ :=
  ∫ s in (0:ℝ)..1,|profileCoeff (γ.splitGrid t n) s-γ.cutoff s|
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
noncomputable def profileHeight : HeatProfile → ℝ
  | [] => 0
  | p::l => max (p.2:ℝ) (profileHeight l)
noncomputable def splitSmoothParameter (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ :=
  n+1+profileHeight (γ.splitGrid t n)
noncomputable def splitSmooth (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ → ℝ → ℝ :=
  profileValue (logCoshTerminal (splitSmoothParameter γ t n)) (γ.splitGrid t n)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
noncomputable def splitTerminal (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ → ℝ :=
  profileValue (logCoshTerminal (splitSmoothParameter γ t n))
    (γ.splitSegment t 1 t.property.2.le n) 0
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_UniformError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
noncomputable def uniformDistance {A:Type*} (f g:A → ℝ) : ℝ := sSup (range (fun x ↦ |f x-g x|))
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_StandardGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def standardGaussian : Measure ℝ := gaussianReal 0 1
noncomputable def gaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι ↦ standardGaussian)

instance instIsProbabilityMeasureRealStandardGaussian : IsProbabilityMeasure standardGaussian := by unfold standardGaussian; infer_instance
instance instIsProbabilityMeasureForallRealGaussianProduct {ι : Type*} [Fintype ι] : IsProbabilityMeasure (gaussianProduct ι) := by
  unfold gaussianProduct; infer_instance

noncomputable def partition {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

noncomputable def gibbsWeight {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (x i) / partition x

noncomputable def logPartition {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.log (partition x)

noncomputable def linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (z : κ → ℝ) (i : ι) : ℝ :=
  ∑ k, c i k*z k

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RotatedCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def rotatedCoefficients {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) : ℝ :=
  Real.cos t*a i k + Real.sin t*b i k

noncomputable def rotationVelocity {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) : ℝ :=
  -Real.sin t*a i k + Real.cos t*b i k

noncomputable def finiteMaximum {ι : Type*} (x : ι → ℝ) : ℝ := sSup (Set.range x)

noncomputable def embedLeft {ι κ ν : Type*} (a : ι → κ → ℝ) (i : ι) : κ ⊕ ν → ℝ :=
  Sum.elim (a i) (fun _ ↦ 0)
noncomputable def embedRight {ι κ ν : Type*} (b : ι → ν → ℝ) (i : ι) : κ ⊕ ν → ℝ :=
  Sum.elim (fun _ ↦ 0) (b i)

noncomputable def spin (b : Bool) : ℝ := if b then 1 else -1
noncomputable def hamiltonian (n : ℕ) (J : (Fin n × Fin n) → ℝ)
    (σ : Fin n → Bool) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i : Fin n, ∑ j : Fin n, if i < j then J (i,j) * spin (σ i) * spin (σ j) else 0
noncomputable def groundStateSequence (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∫ J, sSup (range (hamiltonian n J)) ∂gaussianProduct (Fin n × Fin n)
noncomputable def groundStateValue : ℝ := limUnder atTop groundStateSequence

noncomputable def hamCoeff (n : ℕ) (σ : Fin n → Bool) (k : Fin n × Fin n) : ℝ :=
  if k.1 < k.2 then (Real.sqrt (n : ℝ))⁻¹ * spin (σ k.1) * spin (σ k.2) else 0
noncomputable def expectedMaximum (n : ℕ) : ℝ :=
  ∫ J, finiteMaximum (linearProcess (hamCoeff n) J) ∂gaussianProduct (Fin n × Fin n)

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BlockCoeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def blockCoeff (n m : ℕ) (σ : Fin (n+m) → Bool) :
    (Fin n × Fin n) ⊕ (Fin m × Fin m) → ℝ :=
  Sum.elim (hamCoeff n (fun i ↦ σ (Fin.castAdd m i)))
    (hamCoeff m (fun i ↦ σ (Fin.natAdd n i)))

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_AffineComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def leafFieldCoeff {Λ κ : Type*} (n : ℕ) (v : Λ → κ → ℝ)
    (p : (Fin n → Bool)×Λ) (k : Fin n×κ) : ℝ := spin (p.1 k.1)*v p.2 k.2

noncomputable def leafAuxCoeff {Λ κ : Type*} (n : ℕ) (v : Λ → κ → ℝ)
    (α : Λ) (k : κ×κ) : ℝ := Real.sqrt ((n : ℝ)/2)*v α k.1*v α k.2

noncomputable def guerraCoeff {Λ κ : Type*} (n : ℕ) (v : Λ → κ → ℝ)
    (p : (Fin n → Bool)×Λ) : (Fin n×Fin n) ⊕ (κ×κ) → ℝ :=
  Sum.elim (hamCoeff n p.1) (leafAuxCoeff n v p.2)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GaussianColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable {κ : Type*} [Fintype κ]

noncomputable def columnResidual (v w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ :=
  w-⟪v,w⟫ • v

noncomputable def columnVector (v w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ :=
  ⟪v,w⟫ • columnResidual v w + (⟪v,w⟫^2/Real.sqrt 2) • v

noncomputable def quadraticCoeff (w : EuclideanSpace ℝ κ) (k : κ×κ) : ℝ :=
  w k.1*w k.2/Real.sqrt 2

noncomputable def columnSplitCoeff (v w : EuclideanSpace ℝ κ) : κ ⊕ (κ×κ) → ℝ :=
  Sum.elim (fun k ↦ columnVector v w k) (quadraticCoeff (columnResidual v w))

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

noncomputable def quadraticValue (w : ι → EuclideanSpace ℝ κ) (d : ι → ℝ) : ℝ :=
  ∫ z,finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w i)) z i+d i)
     ∂gaussianProduct (κ×κ)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RandomColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable (κ : Type*) [Fintype κ]

abbrev ColumnHistory (j : ℕ) := Fin j → κ → ℝ
noncomputable def columnHistoryLaw (j : ℕ) : Measure (ColumnHistory κ j) :=
  Measure.pi (fun _ ↦ gaussianProduct κ)
instance instIsProbabilityMeasureColumnHistoryColumnHistoryLaw (j : ℕ) : IsProbabilityMeasure (columnHistoryLaw κ j) := by
  unfold columnHistoryLaw; infer_instance

def historyInit {j : ℕ} (h : ColumnHistory κ (j+1)) : ColumnHistory κ j := fun i ↦ h i.castSucc

def historySplit (j : ℕ) : ColumnHistory κ (j+1) ≃ᵐ ColumnHistory κ j × (κ → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j+1) ↦ κ → ℝ) (Fin.last j)).trans
    MeasurableEquiv.prodComm

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_AdaptiveColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

noncomputable def adaptiveResidual (w : ι → EuclideanSpace ℝ κ)
    (v : (j : ℕ) → ColumnHistory κ j → EuclideanSpace ℝ κ) :
    (j : ℕ) → ColumnHistory κ j → ι → EuclideanSpace ℝ κ
  | 0, _, i => w i
  | j+1,h,i => columnResidual (v j (historyInit κ h))
      (adaptiveResidual w v j (historyInit κ h) i)

noncomputable def adaptiveOffset (w : ι → EuclideanSpace ℝ κ)
    (v : (j : ℕ) → ColumnHistory κ j → EuclideanSpace ℝ κ) :
    (j : ℕ) → ColumnHistory κ j → ι → ℝ
  | 0, _, _ => 0
  | j+1,h,i => adaptiveOffset w v j (historyInit κ h) i+
      linearProcess (fun i k ↦ columnVector (v j (historyInit κ h))
        (adaptiveResidual w v j (historyInit κ h) i) k) (h (Fin.last j)) i

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_ExponentialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SKValueG

instance expOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

instance expOneNoAtoms : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  infer_instance

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SKValueG

noncomputable def gumbelLaw : Measure ℝ := (expMeasure 1).map (fun x ↦ -Real.log x)

instance gumbelProbability : IsProbabilityMeasure gumbelLaw := by
  unfold gumbelLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def gumbelMean : ℝ := ∫ x, x ∂gumbelLaw

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GumbelMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

noncomputable def logSumExp {ι : Type*} [Fintype ι] (d : ι → ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (d i))

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace SKValueG

noncomputable def empiricalMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n+1), X i ω)/(n+1 : ℝ)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GumbelReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

noncomputable def gumbelSmooth (m : ℝ) (ψ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ g, ψ (g/m+s) ∂gumbelLaw

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

noncomputable def gumbelExpMoment (p : ℝ) : ℝ := ∫ g,Real.exp (p*g) ∂gumbelLaw

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BranchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def branchMax (m : ℝ) (b : ℕ)
    (p : (Fin (b+1) → ℝ) × (Fin (b+1) → ℝ)) : ℝ :=
  finiteMaximum (fun i ↦ p.1 i+p.2 i/m)-Real.log (b+1 : ℝ)/m

noncomputable def branchLaw (μ : Measure ℝ) (m : ℝ) (b : ℕ) : Measure ℝ :=
  Measure.map (branchMax m b)
    ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw)))

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GaussianTree
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

structure TreeLevel where
  branchExcess : ℕ
  endpoint : ℝ
  height : ℝ

abbrev GaussianTree := List TreeLevel

abbrev TreeLeaves : GaussianTree → Type
  | [] => PUnit
  | l::T => Fin (l.branchExcess+1) × TreeLeaves T

abbrev TreeEdges : GaussianTree → Type
  | [] => PEmpty
  | l::T => Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T)

instance treeLeavesFintype (T : GaussianTree) : Fintype (TreeLeaves T) := by
  induction T with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons l T ih => exact inferInstanceAs (Fintype (Fin (l.branchExcess+1) × TreeLeaves T))
instance treeLeavesNonempty (T : GaussianTree) : Nonempty (TreeLeaves T) := by
  induction T with
  | nil => exact inferInstanceAs (Nonempty PUnit)
  | cons l T ih => exact inferInstanceAs (Nonempty (Fin (l.branchExcess+1) × TreeLeaves T))
instance treeEdgesFintype (T : GaussianTree) : Fintype (TreeEdges T) := by
  induction T with
  | nil => exact inferInstanceAs (Fintype PEmpty)
  | cons l T ih => exact inferInstanceAs (Fintype (Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T)))

noncomputable def treePathCoeff (c : ℝ → TreeLevel → ℝ) (q : ℝ) :
    (T : GaussianTree) → TreeLeaves T → TreeEdges T → ℝ
  | [],_,e => PEmpty.elim e
  | l::T,α,e => match e with
    | Sum.inl i => if α.1=i then c q l else 0
    | Sum.inr (i,e) => if α.1=i then treePathCoeff c l.endpoint T α.2 e else 0

noncomputable def treeOverlap (q : ℝ) : (T : GaussianTree) → TreeLeaves T → TreeLeaves T → ℝ
  | [],_,_ => q
  | l::T,α,β => if α.1=β.1 then treeOverlap l.endpoint T α.2 β.2 else q

def ValidTreeGrid (q : ℝ) : GaussianTree → Prop
  | [] => q=1
  | l::T => q≤l.endpoint ∧ ValidTreeGrid l.endpoint T

noncomputable def treeFieldVector (q : ℝ) (T : GaussianTree) : TreeLeaves T → TreeEdges T → ℝ :=
  treePathCoeff (fun q l ↦ Real.sqrt (l.endpoint-q)) q T

noncomputable def treeAuxVector (n : ℕ) (q : ℝ) (T : GaussianTree) : TreeLeaves T → TreeEdges T → ℝ :=
  treePathCoeff (fun q l ↦ Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)) q T

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalVectors
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω : Type*}

noncomputable def empiricalVector (f : Ω → ℝ) (x : ℕ → Ω) (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i : Fin n ↦ f (x i))

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable (K n : ℕ)

def paddedRow {j : ℕ} (h : ColumnHistory (Fin n) j) (i : Fin n) : Fin (K+1) → ℝ :=
  fun l ↦ if hl : l.val<j then h ⟨l.val,hl⟩ i else 0

noncomputable def rawHistory (f : ℕ → (Fin (K+1) → ℝ) → ℝ) {j : ℕ}
    (h : ColumnHistory (Fin n) j) (l : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i ↦ f l (paddedRow K n h i))

noncomputable def predictableDirection (f : ℕ → (Fin (K+1) → ℝ) → ℝ) :
    (j : ℕ) → ColumnHistory (Fin n) j → EuclideanSpace ℝ (Fin n)
  | 0,_ => 0
  | j+1,h => gramSchmidtNormed ℝ (rawHistory K n f h) j

def rowColumn (x : Fin n → Fin (K+1) → ℝ) (j : ℕ) (i : Fin n) : ℝ :=
  if hj : j<K+1 then x i ⟨j,hj⟩ else 0

def rowHistory (x : Fin n → Fin (K+1) → ℝ) (j : ℕ) : ColumnHistory (Fin n) j :=
  fun l ↦ rowColumn K n x l.val

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GramSchmidtLimit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def orthogonalRemainder (v : ℕ → E) (w : E) (j : ℕ) : E :=
  w-∑ i∈Finset.range j,(⟪v i,w⟫ : ℝ) • v i

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_QuadraticSK
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

noncomputable def spinVector (n : ℕ) (s : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ spin (s i))

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable (K n : ℕ) (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
  (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
  (x : ℕ → (Fin (K+1) → ℝ))

noncomputable def empiricalColumnEnergy (F : (Fin (K+1) → ℝ) → ℝ) (j : ℕ) : ℝ :=
  ⟪columnVector (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j)
      (orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n))
        (empiricalVector F x n) j),
    empiricalVector (fun y ↦ if hj : j+1<K+1 then y ⟨j+1,hj⟩ else 0) x n⟫

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GaussianTranspose
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

variable (κ ν : Type*) [Fintype κ] [Fintype ν]

def uncurryGaussian : (κ → ν → ℝ) ≃ᵐ ((κ×ν) → ℝ) where
  toFun f k := f k.1 k.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun f : κ → ν → ℝ ↦ fun k : κ×ν ↦ f k.1 k.2)
    fun_prop
  measurable_invFun := by
    change Measurable (fun f : (κ×ν) → ℝ ↦ fun i j ↦ f (i,j))
    fun_prop

def transposeGaussian : (κ → ν → ℝ) ≃ᵐ (ν → κ → ℝ) :=
  (uncurryGaussian κ ν).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : ν×κ ↦ ℝ) (Equiv.prodComm κ ν)).trans
      (uncurryGaussian ν κ).symm)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

def rowSpin (K n : ℕ) (F : (Fin (K+1) → ℝ) → Bool)
    (h : ColumnHistory (Fin n) (K+1)) : Fin n → Bool :=
  fun i ↦ F (paddedRow K n h i)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RoundingSpin
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def boolSign (x : ℝ) : Bool := if 0≤x then true else false

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_LiteralLower
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def leafField {Λ κ : Type*} [Fintype κ] {n : ℕ}
    (v : Λ → κ → ℝ) (z : Fin n×κ → ℝ) (α : Λ) (i : Fin n) : ℝ :=
  ∑ k, v α k*z (i,k)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_TreeGuerra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def treeCenter : GaussianTree → ℝ
  | [] => 0
  | l::T => Real.log (l.branchExcess+1 : ℝ)/l.height+treeCenter T

noncomputable def treeOffset (T : GaussianTree) (g : TreeEdges T → ℝ) (α : TreeLeaves T) : ℝ :=
  linearProcess (treePathCoeff (fun _ l ↦ 1/l.height) 0 T) g α-treeCenter T

noncomputable def scalarTreeValue (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree)
    (z g : TreeEdges T → ℝ) : ℝ :=
  finiteMaximum (fun α ↦ linearProcess (treePathCoeff c q T) z α+treeOffset T g α)

noncomputable def fieldTreeValue (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ)
    (z : Fin n × TreeEdges T → ℝ) (g : TreeEdges T → ℝ) : ℝ :=
  finiteMaximum (fun α ↦ (∑ i,|x i+leafField (treeFieldVector q T) z α i|)+treeOffset T g α)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_TreeProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def gaussianAddLaw (c : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (standardGaussian.prod μ).map (fun p : ℝ×ℝ ↦ c*p.1+p.2)

instance gaussianAddLaw_probability (c : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaussianAddLaw c μ) := by
  unfold gaussianAddLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def edgeNoiseLaw : Measure (ℝ×ℝ) := standardGaussian.prod gumbelLaw
instance edgeNoiseLaw_probability : IsProbabilityMeasure edgeNoiseLaw := by
  unfold edgeNoiseLaw; infer_instance

noncomputable def scalarTreeLaw (c : ℝ → TreeLevel → ℝ) (q : ℝ) : GaussianTree → Measure ℝ
  | [] => Measure.dirac 0
  | l::T => branchLaw (gaussianAddLaw (c q l) (scalarTreeLaw c l.endpoint T)) l.height l.branchExcess

noncomputable def scalarTreeEval (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree)
    (w : TreeEdges T → ℝ×ℝ) : ℝ :=
  scalarTreeValue c q T (fun e ↦ (w e).1) (fun e ↦ (w e).2)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_CascadeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

abbrev CascadeShape := List (ℝ×ℝ)
abbrev CascadeWidths : CascadeShape → Type
  | [] => PUnit
  | _::L => ℕ×CascadeWidths L

noncomputable def cascadeLaw : (L : CascadeShape) → CascadeWidths L → Measure ℝ
  | [],_ => Measure.dirac 0
  | (c,m)::L,w => branchLaw (gaussianAddLaw c (cascadeLaw L w.2)) m w.1

def CascadeScale (a : ℝ) : CascadeShape → Prop
  | [] => 0 ≤ a
  | (_,m)::L => 0 ≤ a ∧ a < m ∧ CascadeScale m L

noncomputable def cascadeMoment (a : ℝ) : CascadeShape → ℝ
  | [] => 1
  | (c,m)::L => gumbelExpMoment (a/m)*(Real.exp ((m*c)^2/2)*cascadeMoment m L)^(a/m)

noncomputable def cascadeMean : CascadeShape → ℝ
  | [] => 0
  | (c,m)::L => gumbelMean/m+Real.log (Real.exp ((m*c)^2/2)*cascadeMoment m L)/m

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_FieldTreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def fieldNoiseLaw (n : ℕ) : Measure ((Fin n → ℝ)×ℝ) :=
  (gaussianProduct (Fin n)).prod gumbelLaw
instance fieldNoiseLaw_probability (n : ℕ) : IsProbabilityMeasure (fieldNoiseLaw n) := by
  unfold fieldNoiseLaw; infer_instance

noncomputable def fieldTreeEval (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ)
    (w : TreeEdges T → (Fin n → ℝ)×ℝ) : ℝ :=
  fieldTreeValue n q T x (fun p ↦ (w p.2).1 p.1) (fun e ↦ (w e).2)

noncomputable def fieldChildLaw (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) : Measure ℝ :=
  ((gaussianProduct (Fin n)).prod (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n))).map
    (fun p ↦ fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2)

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RandomGuerra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def fieldProfile (q : ℝ) : GaussianTree → ℝ → ℝ
  | [] => abs
  | l::T => SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T)

def TreeScale (a : ℝ) : GaussianTree → Prop
  | [] => 0 ≤ a
  | l::T => 0 ≤ a ∧ a < l.height ∧ TreeScale l.height T

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BranchMeanUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def gumbelTreeMoment (a : ℝ) : GaussianTree → ℝ
  | [] => 1
  | l::T => gumbelExpMoment (a/l.height)*(gumbelTreeMoment l.height T)^(a/l.height)

noncomputable def gumbelTreeMean : GaussianTree → ℝ
  | [] => 0
  | l::T => gumbelMean/l.height+Real.log (gumbelTreeMoment l.height T)/l.height

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_TreeWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def auxAmplitude (n : ℕ) (q : ℝ) (l : TreeLevel) : ℝ :=
  Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)

noncomputable def auxShape (n : ℕ) (q : ℝ) : GaussianTree → CascadeShape
  | [] => []
  | l::T => (auxAmplitude n q l,l.height)::auxShape n l.endpoint T

noncomputable def resizeTree (n : ℕ) (q : ℝ) : (T : GaussianTree) → CascadeWidths (auxShape n q T) → GaussianTree
  | [],_ => []
  | l::T,w => {l with branchExcess := w.1}::resizeTree n l.endpoint T w.2

noncomputable def treeCorrection (q : ℝ) : GaussianTree → ℝ
  | [] => 0
  | l::T => l.height*(l.endpoint^2-q^2)/4+treeCorrection l.endpoint T

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_CascadePassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def profileTree (q : ℝ) : SKValue.HeatProfile → GaussianTree
  | [] => []
  | p::l => ⟨0,q+p.1,p.2⟩::profileTree (q+p.1) l

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CrossMeshComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def ordinaryMeshSource (T : ℝ) (N : ℕ) (γ β : ℝ → ℝ) (V : ℝ → ℝ → ℝ) : ℝ :=
  stepSize T N*∑ j : Fin N,(β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j))
      (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1)))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Volterra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter Function
open scoped Topology NNReal Nat
namespace SKValue
structure VolterraData (T:ℝ) (hT:0≤T) where
  field:ℝ → ℝ → ℝ
  lip:ℝ≥0
  bound:∀t∈Icc (0:ℝ) T,∀x y,dist (field t x) (field t y)≤lip*dist x y
  integ:∀Y:C(Icc (0:ℝ) T,ℝ),IntervalIntegrable (fun s ↦ field s (Y (projIcc 0 T hT s))) volume 0 T
namespace VolterraData
variable {T:ℝ} {hT:0≤T} (D:VolterraData T hT)
noncomputable def next (Y:C(Icc (0:ℝ) T,ℝ)):C(Icc (0:ℝ) T,ℝ) where
  toFun t:=∫s in (0:ℝ)..(t:ℝ),D.field s (Y (projIcc 0 T hT s))
  continuous_toFun:=by
    have hc:=intervalIntegral.continuousOn_primitive_interval' (D.integ Y) left_mem_uIcc
    rw [uIcc_of_le hT] at hc
    exact hc.domRestrict
end VolterraData
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_EulerLimitProcess
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
noncomputable def eulerLimitProcess (W:BrownianSpace) (γ:OrderParameter) (t:ℝ) (z:W.Ω):ℝ :=
  if 0<t ∧ t<1 then limsup (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop else 0
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_DiffusionExistence
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
noncomputable def terminalEulerProcess (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω):ℝ :=
  limsup (fun n:ℕ ↦ eulerLimitProcess W γ (terminalTime n) z) atTop
noncomputable def diffusionProcess (W:BrownianSpace) (γ:OrderParameter) (t:ℝ) (z:W.Ω):ℝ :=
  if t<1 then eulerLimitProcess W γ t z else terminalEulerProcess W γ z
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_WeightedMoments
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def weightedEulerMoment (W : BrownianSpace) (γ η : OrderParameter)
    (T : ℝ) (N : ℕ) : ℝ :=
  stepSize T N*∑ j : Fin N,η.coeff (meshTime T N j)*
    (∫ z,(1/2 : ℝ)*(gradient W γ (meshTime T N j)
      (euler T N γ.coeff (gradient W γ) z j))^2 ∂gaussianProduct (Fin (N+1)))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_OrderVariations
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def OrderParameter.mix (γ η : OrderParameter) (ε : ℝ)
    (hε : ε∈Icc (0 : ℝ) 1) : OrderParameter where
  coeff t := (1-ε)*γ.coeff t+ε*η.coeff t
  nonneg t ht := add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (γ.nonneg t ht))
    (mul_nonneg hε.1 (η.nonneg t ht))
  monotone _s hs _t ht hst := add_le_add
    (mul_le_mul_of_nonneg_left (γ.monotone hs ht hst) (sub_nonneg.mpr hε.2))
    (mul_le_mul_of_nonneg_left (η.monotone hs ht hst) hε.1)
  rightContinuous t ht := ((γ.rightContinuous t ht).const_mul _).add ((η.rightContinuous t ht).const_mul _)
  integrable := (γ.integrable.const_mul _).add (η.integrable.const_mul _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def gradientMoment (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (t : ℝ) : ℝ := ∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_ContactVariations
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def OrderParameter.add (γ η : OrderParameter) : OrderParameter where
  coeff t := γ.coeff t+η.coeff t
  nonneg t ht := add_nonneg (γ.nonneg t ht) (η.nonneg t ht)
  monotone _ hs _ ht hst := add_le_add (γ.monotone hs ht hst) (η.monotone hs ht hst)
  rightContinuous t ht := (γ.rightContinuous t ht).add (η.rightContinuous t ht)
  integrable := γ.integrable.add η.integrable

noncomputable def OrderParameter.atom (s : ℝ) : OrderParameter where
  coeff t := if s≤t then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  monotone t _ u _ htu := by
    by_cases hst : s≤t
    · simp only [ite_eq_left hst,ite_eq_left (hst.trans htu),le_refl]
    · simp only [ite_eq_right hst]; split_ifs <;> norm_num
  rightContinuous t _ := by
    by_cases hst : s≤t
    · apply (continuousWithinAt_const (b := (1 : ℝ))).congr
      · intro u hu
        exact ite_eq_left (hst.trans hu)
      · exact ite_eq_left hst
    · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hst))] with u hu
        exact ite_eq_right (not_le.mpr hu)
      · exact ite_eq_right hst
  integrable := by
    apply Integrable.of_bound
      (StronglyMeasurable.ite measurableSet_Ici stronglyMeasurable_const stronglyMeasurable_const).aestronglyMeasurable 1
    exact Eventually.of_forall (fun t ↦ by split_ifs <;> norm_num)

noncomputable def OrderParameter.removeBelow (γ : OrderParameter) (c : ℝ) : OrderParameter where
  coeff t := max (γ.coeff t-c) 0
  nonneg _ _ := le_max_right _ _
  monotone _ hs _ ht hst := max_le_max (sub_le_sub_right (γ.monotone hs ht hst) c) le_rfl
  rightContinuous t ht := ((γ.rightContinuous t ht).sub continuousWithinAt_const).sup continuousWithinAt_const
  integrable := (γ.integrable.sub (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1) (C := c) (by simp))).sup integrableOn_zero

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def contactPotential (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ t in s..1,gradientMoment W γ X t-t

end SKValue

end

end OAI
end


