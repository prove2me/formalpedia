-- Prove2me | Definitions.Def_Q226II002
-- name    : Q226II002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:33:34.474428+00:00
-- url     : https://prove2.me/theorems/dc087141-5dfb-4cb3-89d6-38c3a4e19567
-- title:
--   Definitions bundle Q226II002 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 72 declarations of OpenAI's Lean: 20 definitions, 8 instances and 44 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.height`, `OAI.SmoothLocal.HighEquation.QSpatialState`, `OAI.SmoothLocal.HighEquation.comparisonEnergyRate`, `OAI.SmoothLocal.HighEquation.comparisonEnergySpeed`, `OAI.SmoothLocal.HighEquation.initialCutEnergyBudget`, `OAI.SmoothLocal.HighEquation.qSpatialAxis`, `OAI.SmoothLocal.HighEquation.qSpatialIndex`, `OAI.SmoothLocal.HighEquation.spatialEnergyNormBudget`, `OAI.SmoothLocal.Hyperbolic.firstJetSliceBudget`, `OAI.SmoothLocal.Pulse.CurvatureFirstInput`, `OAI.SmoothLocal.Pulse.boundedClassShearedStateBudget`, `OAI.SmoothLocal.Pulse.curvatureFirstDomain`, `OAI.SmoothLocal.Pulse.curvatureFirstTube`, `OAI.SmoothLocal.Pulse.finiteCapRequiredMetricOrder`, `OAI.SmoothLocal.Pulse.forcingFloor`, `OAI.SmoothLocal.Taylor.normalizedTimePower`, `OAI.SmoothLocal.Taylor.taylorInitialRequest`, `OAI.SmoothLocal.Taylor.taylorStripJetOrder`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Calculus_BoundedClassInitialJet`, `IsometricImmersion_Calculus_MovingFirstJetBase`, `IsometricImmersion_Caps_ActualFiniteCapMetricBounds`, `IsometricImmersion_Caps_PulseCapSeparation`, `IsometricImmersion_Comparison_ActualComparisonEnergy`, `IsometricImmersion_Comparison_ActualComparisonSource`, `IsometricImmersion_Comparison_ComparisonEnergyScaling`, `IsometricImmersion_Comparison_ComparisonPulseGeometry`, `IsometricImmersion_Comparison_ShearFirstJetComparison`, `IsometricImmersion_Curvature_CurvatureLowerTube`, `IsometricImmersion_Darboux_QFirstJetEnergy`, `IsometricImmersion_Darboux_QInitialEnergy`, `IsometricImmersion_Darboux_QSpatialRestriction`, `IsometricImmersion_Energy_MovingEnergyGradient`, `IsometricImmersion_Energy_MovingIntervalSourceL2`, `IsometricImmersion_Metric`, `IsometricImmersion_Pulses_ForcingCoefficientSign`, `IsometricImmersion_Pulses_PulseActualDensity`, `IsometricImmersion_Pulses_PulseMoment`, `IsometricImmersion_Pulses_PulseScalarContradiction`, `IsometricImmersion_Taylor_TaylorPolynomialJetBounds`, `IsometricImmersion_Taylor_TaylorRemainderBound`, `IsometricImmersion_Taylor_TimeTaylorKernel`, `IsometricImmersion_Taylor_UniformTaylorPolynomial`, `IsometricImmersion_Taylor_UniformTaylorPulse`, `IsometricImmersion_Taylor_UniformTaylorStrip`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`.
--
--   **Imported by** (directly, in this split): the bundles `Q226II005` and `Q226II006`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion

section
-- module Solutions.Q226_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace SmoothLocal.Geometry

def height (F : Coord → Ambient) (e : Ambient) : Coord → ℝ :=
  fun p => inner ℝ (F p) e

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureLowerTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

abbrev CurvatureFirstInput := (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → Fin 2 → ℝ)

def curvatureFirstDomain : Set CurvatureFirstInput := {a | (Matrix.of a.1).det ≠ 0}
def curvatureFirstTube (M d : ℝ) : Set CurvatureFirstInput :=
  Metric.closedBall 0 M ∩ (fun a : CurvatureFirstInput => (Matrix.of a.1).det) ⁻¹' Ici d

theorem curvatureFirstDet_contDiff :
    ContDiff ℝ ∞ (fun a : CurvatureFirstInput => (Matrix.of a.1).det) := by
  simp only [Matrix.det_fin_two,Matrix.of_apply]
  fun_prop

theorem curvatureFirstDomain_isOpen : IsOpen curvatureFirstDomain :=
  isOpen_ne_fun curvatureFirstDet_contDiff.continuous continuous_const

theorem curvatureFirstTube_isCompact (M d : ℝ) : IsCompact (curvatureFirstTube M d) :=
  (isCompact_closedBall (0 : CurvatureFirstInput) M).inter_right
    (isClosed_Ici.preimage curvatureFirstDet_contDiff.continuous)

theorem curvatureFirstTube_subset_domain (M : ℝ) {d : ℝ} (hd : 0 < d) :
    curvatureFirstTube M d ⊆ curvatureFirstDomain := by
  intro a ha
  exact ne_of_gt (hd.trans_le ha.2)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseActualDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem approximation_budget_le_pulse_error {N n : ℕ}
    (hN : 0 < N) (hn : 1 ≤ n) (hlarge : N-1 ≤ n) :
    1/(n : ℝ)^n ≤ (n : ℝ)/(n : ℝ)^N := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  calc
    _ ≤ 1/(n : ℝ)^(N-1) :=
      one_div_le_one_div_of_le (pow_pos hn0 _) (pow_le_pow_right₀ hn1 hlarge)
    _ = (n : ℝ)/(n : ℝ)^N := by
      have hN' : N = (N-1)+1 := by omega
      conv_rhs => rw [hN',pow_add,pow_one]
      field_simp [hn0.ne']

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ShearFirstJetComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem abs_sum_fin_two_le {f : Fin 2 → ℝ} {e : ℝ}
    (hf : ∀ i, |f i| ≤ e) : |∑ i, f i| ≤ 2*e := by
  simp only [Fin.sum_univ_two]
  exact ((abs_add_le _ _).trans (add_le_add (hf 0) (hf 1))).trans_eq (by ring)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingEnergyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.ODE

theorem scalar_gradient_le_energy {s0 S a b : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S) :
    a ^ 2 + b ^ 2 ≤ (2 * (1 + 1 / s0)) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hspos : 0 ≤ S := hs0.le.trans hS
  have hsb : b ^ 2 ≤ (S * b ^ 2) / s0 := (le_div_iff₀ hs0).2
    (by nlinarith [mul_le_mul_of_nonneg_right hS (sq_nonneg b)])
  have hsb' : b ^ 2 ≤ (1 / s0) * (S * b ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using hsb
  have hi : 0 ≤ 1 / s0 := by positivity
  nlinarith [mul_nonneg hi (sq_nonneg a), mul_nonneg hspos (sq_nonneg b)]

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MovingIntervalSourceL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.ODE

theorem real_interval_coefficient_eLpNorm_two
    {a f : ℝ → ℝ} {left right C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x ∈ Icc left right, |a x| ≤ C) :
    eLpNorm' (fun x => a x * f x) (2 : ℝ) (volume.restrict (Icc left right)) ≤
      ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict (Icc left right)) := by
  have hdom : ∀ᵐ x ∂volume.restrict (Icc left right), ‖a x * f x‖ ≤ ‖C * f x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha x hx) (abs_nonneg _)
  calc
    _ ≤ eLpNorm' (fun x => C * f x) (2 : ℝ) (volume.restrict (Icc left right)) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f) C (by norm_num)

theorem real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    {coefficient factor : ℝ → ℝ} {left right bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ point ∈ Icc left right, |coefficient point| ≤ bound)
    (hmeas : AEStronglyMeasurable (fun point => coefficient point * factor point)
      (volume.restrict (Icc left right))) :
    eLpNorm (fun point => coefficient point * factor point) 2
      (volume.restrict (Icc left right)) ≤
      ‖bound‖ₑ * eLpNorm factor 2 (volume.restrict (Icc left right)) := by
  have hfactor : eLpNorm' factor (2 : ℝ) (volume.restrict (Icc left right)) ≤
      eLpNorm factor 2 (volume.restrict (Icc left right)) := by
    by_cases hfactorMeas : AEStronglyMeasurable factor (volume.restrict (Icc left right))
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
      norm_num
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
      norm_num
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact (real_interval_coefficient_eLpNorm_two hbound hcoefficient).trans
    (mul_le_mul_right hfactor _)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MovingFirstJetBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.ODE

def firstJetSliceBudget (Z widthUpper : ℝ) : ℝ≥0 :=
  (‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ))).toNNReal

theorem firstJetSliceBudget_coe (Z widthUpper : ℝ) :
    (firstJetSliceBudget Z widthUpper : ℝ≥0∞) =
      ‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ)) := by
  exact ENNReal.coe_toNNReal (by finiteness)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Hyperbolic

abbrev QSpatialState := Fin 5 → ℝ

def qSpatialAxis : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]
def qSpatialIndex : Fin 6 → Fin 5 := ![0, 0, 1, 2, 3, 4]

theorem qSpatialAxis_index {i : Fin 6} (hi : i ≠ 1) : qSpatialAxis (qSpatialIndex i) = i := by
  fin_cases i <;> first | rfl | exact (hi rfl).elim

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstJetEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Hyperbolic

def spatialEnergyNormBudget (s0 : ℝ) (A : ℝ≥0) : ℝ≥0 :=
  ⟨Real.sqrt (2 * (1 + 1 / s0)) * (A : ℝ), mul_nonneg (Real.sqrt_nonneg _) A.2⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QInitialEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Hyperbolic

def initialCutEnergyBudget (width M : ℝ) (A : ℝ≥0) : ℝ≥0 :=
  ⟨Real.sqrt (width * (1 + M) / 2) * (A : ℝ), mul_nonneg (Real.sqrt_nonneg _) A.2⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TimeTaylorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Function Set
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Taylor

def normalizedTimePower (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (t - a)^m / (m.factorial : ℝ)

theorem normalizedTimePower_contDiff (a : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (normalizedTimePower a m) := by
  unfold normalizedTimePower
  fun_prop

theorem normalizedTimePower_hasDerivAt (a t : ℝ) (m : ℕ) :
    HasDerivAt (normalizedTimePower a (m + 1)) (normalizedTimePower a m t) t := by
  have h := (((hasDerivAt_id t).sub_const a).pow (m + 1)).div_const ((m + 1).factorial : ℝ)
  change HasDerivAt (normalizedTimePower a (m + 1))
    ((m + 1 : ℕ) * (t - a)^(m + 1 - 1) * 1 / ((m + 1).factorial : ℝ)) t at h
  simp only [Nat.add_sub_cancel, mul_one] at h
  have he : (m + 1 : ℕ) * (t - a)^m / ((m + 1).factorial : ℝ) = normalizedTimePower a m t := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, normalizedTimePower]
    have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hm, hm1]
  rw [he] at h
  exact h

theorem normalizedTimePower_deriv (a : ℝ) (m : ℕ) :
    deriv (normalizedTimePower a (m + 1)) = normalizedTimePower a m := by
  funext t
  exact (normalizedTimePower_hasDerivAt a t m).deriv

theorem normalizedTimePower_iteratedDeriv_at_center (a : ℝ) (m k : ℕ) :
    iteratedDeriv k (normalizedTimePower a m) a = if k = m then 1 else 0 := by
  change iteratedDeriv k (fun t : ℝ => (t - a)^m / (m.factorial : ℝ)) a = _
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_sub_const (f := fun t : ℝ => t^m)]
  change iteratedDeriv k (fun t : ℝ => t^m) (a - a) / (m.factorial : ℝ) = _
  rw [sub_self, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℝ) ≠ 0)
  · simpa only [Nat.cast_zero] using (zero_div (m.factorial : ℝ))

theorem coefficient_timePower_jet (a C : ℝ) (m k : ℕ) :
    iteratedDeriv k (fun t => C * normalizedTimePower a m t) a =
      if k = m then C else 0 := by
  rw [iteratedDeriv_const_mul_field, normalizedTimePower_iteratedDeriv_at_center]
  split_ifs <;> simp

section Composition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedDeriv_comp_eq_of_jets {Q : E → F} {f g : ℝ → E} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ∞ f a) (hg : ContDiffAt ℝ ∞ g a)
    (hQ : ContDiffAt ℝ ∞ Q (f a))
    (hjets : ∀ j ≤ n, iteratedDeriv j f a = iteratedDeriv j g a) :
    iteratedDeriv n (Q ∘ f) a = iteratedDeriv n (Q ∘ g) a := by
  have hvalue : f a = g a := by simpa only [iteratedDeriv_zero] using hjets 0 (Nat.zero_le n)
  have hQg : ContDiffAt ℝ ∞ Q (g a) := by rw [← hvalue]; exact hQ
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hQ hf (WithTop.coe_le_coe.mpr le_top),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hQg hg (WithTop.coe_le_coe.mpr le_top)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hvalue]
  congr 1
  funext j
  exact hjets (c.partSize j) (c.partSize_le j)

theorem iteratedDeriv_add_eq_of_zero_jets {f h : ℝ → E} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ∞ f a) (hh : ContDiffAt ℝ ∞ h a)
    (hzero : ∀ j ≤ n, iteratedDeriv j h a = 0) :
    ∀ j ≤ n, iteratedDeriv j (fun t => f t + h t) a = iteratedDeriv j f a := by
  intro j hj
  rw [iteratedDeriv_fun_add (hf.of_le (WithTop.coe_le_coe.mpr le_top))
    (hh.of_le (WithTop.coe_le_coe.mpr le_top)), hzero j hj, add_zero]

end Composition
end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_BoundedClassInitialJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def boundedClassShearedStateBudget (q0 : ℝ) (M : ℕ) : ℝ :=
  max 1 ((2 * (1 + |q0|))^2 * (M : ℝ))

theorem boundedClassShearedStateBudget_pos (q0 : ℝ) (M : ℕ) :
    0 < boundedClassShearedStateBudget q0 M :=
  zero_lt_one.trans_le (le_max_left _ _)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PulseCapSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE
open SmoothLocal.HighEquation

theorem exists_sectionFour_radius {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      M*(r+107*(L*r)/100) ≤ 9/(100*L) := by
  let A := M*(1+107*L/100)
  let alpha := 9/(100*L)
  have hA : 0 ≤ A := by dsimp only [A] <;> positivity
  have ha : 0 < alpha := by dsimp only [alpha] <;> positivity
  let r := min (1/40 : ℝ) (min (1/(20*L)) (alpha/(2*(A+1))))
  have hr : 0 < r := by dsimp only [r] <;> positivity
  have hr1 : r ≤ 1/40 := min_le_left _ _
  have hr2 : r ≤ 1/(20*L) := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ alpha/(2*(A+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hr2' := (le_div_iff₀ (by positivity : 0 < 20*L)).mp hr2
  have hr3' := (le_div_iff₀ (by positivity : 0 < 2*(A+1))).mp hr3
  refine ⟨r,hr,by linarith,by nlinarith,?_⟩
  have he : M*(r+107*(L*r)/100) = A*r := by dsimp only [A] <;> ring
  rw [he]
  change A*r ≤ alpha
  nlinarith

theorem pulse_width_eventually {r : ℝ} (hr : 0 < r) (delta : ℝ) :
    ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧ delta/(2*tau) ≤ r/4 := by
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
  have hw : Tendsto (fun tau : ℝ => delta/(2*tau)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using hi.const_mul (delta/2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hw.eventually_lt tendsto_const_nhds (show (0 : ℝ) < r/4 by linarith)] with tau ht hwidth
  exact ⟨ht,hwidth.le⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualFiniteCapMetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry
open SmoothLocal.ODE SmoothLocal.HighEquation

def finiteCapRequiredMetricOrder (nLower nUpper : ℕ) : ℕ :=
  max (max 8 (nLower+3)) (max 8 (nUpper+3))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ForcingCoefficientSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def forcingFloor (e D C : ℝ) : ℝ := e/(2*max D 1*max C 1)

theorem forcingFloor_pos {e : ℝ} (he : 0 < e) (D C : ℝ) : 0 < forcingFloor e D C := by
  unfold forcingFloor
  have hD : 0 < max D 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hC : 0 < max C 1 := zero_lt_one.trans_le (le_max_right _ _)
  positivity

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse

theorem compact_weight_cos_integral_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ (∫ x : ℝ, |deriv f x|)/tau := by
  let v : ℝ → ℝ := fun x => Real.sin (tau*x)/tau
  have hc : Continuous (fun x : ℝ => Real.cos (tau*x)) := by fun_prop
  have hvcont : Continuous v := by dsimp only [v]; fun_prop
  have hdcont : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hdcompact : HasCompactSupport (deriv f) := hcompact.deriv
  have hfc : Integrable (fun x : ℝ => f x*Real.cos (tau*x)) :=
    (hf.continuous.mul hc).integrable_of_hasCompactSupport hcompact.mul_right
  have hdfv : Integrable (fun x : ℝ => deriv f x*v x) :=
    (hdcont.mul hvcont).integrable_of_hasCompactSupport hdcompact.mul_right
  have hfv : Integrable (fun x : ℝ => f x*v x) :=
    (hf.continuous.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  have hv (x : ℝ) : HasDerivAt v (Real.cos (tau*x)) x := by
    have h := ((Real.hasDerivAt_sin (tau*x)).comp x
      ((hasDerivAt_id x).const_mul tau)).div_const tau
    simp only [Function.comp_def] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | field_simp [htau.ne']
  have hibp : (∫ x : ℝ, f x*Real.cos (tau*x)) = -∫ x : ℝ, deriv f x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
      (fun x _ => hv x) hfc hdfv hfv
  have hdint : Integrable (fun x : ℝ => |deriv f x|) :=
    hdcont.abs.integrable_of_hasCompactSupport hdcompact.abs
  have hnorm : ∀ x : ℝ, ‖deriv f x*v x‖ ≤ |deriv f x| / tau := by
    intro x
    simp only [Real.norm_eq_abs,abs_mul,v,abs_div,abs_of_pos htau]
    calc
      _ ≤ |deriv f x| * (1/tau) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) htau.le) (abs_nonneg _)
      _ = _ := by ring
  rw [hibp,abs_neg]
  have h := norm_integral_le_of_norm_le (hdint.div_const tau) (Eventually.of_forall hnorm)
  simpa only [Real.norm_eq_abs,integral_div] using h

theorem compact_weight_cos_integral_tendsto_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, f x*Real.cos (tau*x)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ tau : ℝ in atTop,
      ‖∫ x : ℝ, f x*Real.cos (tau*x)‖ ≤ (∫ x : ℝ, |deriv f x|)/tau := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    simpa only [Real.norm_eq_abs] using compact_weight_cos_integral_le hf hcompact htau
  have hzero : Tendsto (fun tau : ℝ => (∫ x : ℝ, |deriv f x|)/tau) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0)).const_mul
        (∫ x : ℝ, |deriv f x|)
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hzero

theorem compact_weight_cos_sq_integral_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hcompact : HasCompactSupport f) (tau : ℝ) :
    (∫ x : ℝ, f x*Real.cos (tau*x)^2) =
      (1/2 : ℝ)*(∫ x : ℝ, f x)+
        (1/2 : ℝ)*(∫ x : ℝ, f x*Real.cos ((2*tau)*x)) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcompact
  have hci : Integrable (fun x : ℝ => f x*Real.cos ((2*tau)*x)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hcompact.mul_right
  have heq : (fun x : ℝ => f x*Real.cos (tau*x)^2) =
      fun x => (1/2 : ℝ)*f x+(1/2 : ℝ)*(f x*Real.cos ((2*tau)*x)) := by
    funext x
    have hc : Real.cos ((2*tau)*x) = 2*Real.cos (tau*x)^2-1 := by
      rw [mul_assoc,Real.cos_two_mul]
    rw [hc]
    ring
  rw [heq,integral_add (hfi.const_mul (1/2)) (hci.const_mul (1/2)),
    integral_const_mul,integral_const_mul]

theorem compact_weight_cos_sq_integral_tendsto {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, f x*Real.cos (tau*x)^2) atTop
      (𝓝 ((1/2 : ℝ)*(∫ x : ℝ, f x))) := by
  have hfreq : Tendsto (fun tau : ℝ => 2*tau) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hzero := (compact_weight_cos_integral_tendsto_zero hf hcompact).comp hfreq
  have hlimit := (hzero.const_mul (1/2 : ℝ)).const_add ((1/2 : ℝ)*(∫ x : ℝ, f x))
  simpa only [compact_weight_cos_sq_integral_eq hf.continuous hcompact,
    Function.comp_def,mul_zero,add_zero] using hlimit

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

theorem taylor_moment_absorption_threshold {R c3 : ℝ}
    (hR : 0 ≤ R) (hc3 : 0 < c3) (N : ℕ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ delta : ℝ, 0 ≤ delta →
      R*delta/tau^(N+1) ≤ (c3/2)*delta*tau/tau^N := by
  refine ⟨max 1 (2*R/c3),le_max_left _ _,?_⟩
  intro tau ht delta hdelta
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 2*R/c3 ≤ tau := (le_max_right _ _).trans ht
  have hh := (div_le_iff₀ hc3).mp hthreshold
  have hcoeff : R/tau ≤ (c3/2)*tau := by
    calc
      R/tau ≤ R := div_le_self hR ht1
      _ ≤ (c3/2)*tau := by linarith only [hh]
  have hscale : 0 ≤ delta/tau^N := div_nonneg hdelta (pow_nonneg htpos.le N)
  calc
    _ = (R/tau)*(delta/tau^N) := by rw [pow_succ]; field_simp [htpos.ne']
    _ ≤ ((c3/2)*tau)*(delta/tau^N) := mul_le_mul_of_nonneg_right hcoeff hscale
    _ = _ := by ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

def comparisonEnergySpeed (C : ℝ) : ℝ := C+Real.sqrt C
def comparisonEnergyRate (C Z0 Z s0 : ℝ) : ℝ :=
  8*(C*(max 1 Z0+max 1 Z))*(1+1/s0)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonEnergyScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem comparison_exponential_le_fixed {Lambda delta tau : ℝ}
    (ht : 0 < tau) (hlarge : Lambda*(2*delta) ≤ tau) :
    Real.exp (Lambda*(2*delta/tau)) ≤ Real.exp 1 := by
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc]
  exact (div_le_one ht).mpr hlarge

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonPulseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem comparison_pulse_travel_bound
    {a delta tau speed : ℝ} (ha : 0 < a) (ht : 0 < tau)
    (hlarge : 2*speed*delta/(3*a) ≤ tau) : speed*(2*delta/tau) ≤ 3*a := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht).mpr
  first | (convert (div_le_iff₀ (by positivity : 0 < 3*a)).mp hlarge using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (((div_le_iff₀ (by positivity : 0 < 3*a)).mp hlarge).trans (le_of_eq (by ring)))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseScalarContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace SmoothLocal.Pulse

theorem pulse_moment_bounds_incompatible {m c3 delta tau E C0 C1 : ℝ} (N : ℕ)
    (hc3 : 0 < c3) (hd : 0 < delta) (ht : 0 < tau)
    (hsmall : C0*delta ≤ c3/4)
    (hedge : E ≤ (c3/4)*delta*tau)
    (hlower : C1*delta ≤ (c3/4)*tau)
    (hpositive : c3*delta*tau/tau^N ≤ |m|)
    (hcost : |m| ≤ E/tau^N+C0*delta^2*tau/tau^N+C1*delta^2/tau^N) : False := by
  have hquot : c3*delta*tau/tau^N ≤ (E+C0*delta^2*tau+C1*delta^2)/tau^N := by
    calc
      _ ≤ |m| := hpositive
      _ ≤ _ := hcost
      _ = _ := by ring
  have hnum : c3*delta*tau ≤ E+C0*delta^2*tau+C1*delta^2 :=
    (div_le_div_iff_of_pos_right (pow_pos ht N)).mp hquot
  have hscaled := mul_le_mul_of_nonneg_right hsmall (mul_pos hd ht).le
  have hlowscaled := mul_le_mul_of_nonneg_right hlower hd.le
  have hlead : 0 < c3*delta*tau := mul_pos (mul_pos hc3 hd) ht
  nlinarith

theorem exists_delta_then_frequency_for_moment_contradiction {c3 C0 : ℝ}
    (hc3 : 0 < c3) (hC0 : 0 ≤ C0) (N : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
      ∀ E C1 : ℝ, ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ m : ℝ,
        c3*delta*tau/tau^N ≤ |m| →
        |m| ≤ E/tau^N+C0*delta^2*tau/tau^N+C1*delta^2/tau^N → False := by
  let delta := min (1/4) (c3/(8*(C0+1)))
  have hden : 0 < 8*(C0+1) := by positivity
  have hd : 0 < delta := lt_min (by norm_num) (div_pos hc3 hden)
  have hd1 : delta ≤ 1/4 := min_le_left _ _
  have hd2 : delta ≤ c3/(8*(C0+1)) := min_le_right _ _
  have hsmall : C0*delta ≤ c3/4 := by
    have hh := (le_div_iff₀ hden).mp hd2
    nlinarith
  refine ⟨delta,hd,by linarith,?_⟩
  intro E C1
  let T := max 1 (max (4*E/(c3*delta)) (4*C1*delta/c3))
  refine ⟨T,le_max_left _ _,?_⟩
  intro tau ht m hpositive hcost
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have heT : 4*E/(c3*delta) ≤ tau := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hlT : 4*C1*delta/c3 ≤ tau := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hedge : E ≤ (c3/4)*delta*tau := by
    have hh := (div_le_iff₀ (mul_pos hc3 hd)).mp heT
    nlinarith
  have hlower : C1*delta ≤ (c3/4)*tau := by
    have hh := (div_le_iff₀ hc3).mp hlT
    nlinarith
  exact pulse_moment_bounds_incompatible N hc3 hd htpos hsmall hedge hlower hpositive hcost

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorPolynomialJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem normalizedTimePower_abs_le_one (a t : ℝ) (m : ℕ) (ht : |t - a| ≤ 1) :
    |normalizedTimePower a m t| ≤ 1 := by
  have hpow : |t - a|^m ≤ (1 : ℝ) := pow_le_one₀ (abs_nonneg _) ht
  have hfact : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ m.factorial from Nat.factorial_pos m)
  rw [normalizedTimePower, abs_div, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg m.factorial : (0 : ℝ) ≤ (m.factorial : ℝ))]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hfact)).mpr (by simpa using hpow.trans hfact)

theorem normalizedTimePower_zero (a : ℝ) : normalizedTimePower a 0 = fun _ => (1 : ℝ) := by
  funext t
  simp [normalizedTimePower]

theorem normalizedTimePower_iteratedDeriv_abs_le_one (a t : ℝ) (m k : ℕ)
    (ht : |t - a| ≤ 1) : |iteratedDeriv k (normalizedTimePower a m) t| ≤ 1 := by
  induction k generalizing m with
  | zero => exact normalizedTimePower_abs_le_one a t m ht
  | succ k hk =>
    cases m with
    | zero =>
      rw [normalizedTimePower_zero]
      simp [iteratedDeriv_const]
    | succ m =>
      rw [iteratedDeriv_succ', normalizedTimePower_deriv]
      exact hk m

theorem normalizedTimePower_fullJet_le_one (a t : ℝ) (m k : ℕ)
    (ht : |t - a| ≤ 1) : ‖iteratedFDeriv ℝ k (normalizedTimePower a m) t‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact normalizedTimePower_iteratedDeriv_abs_le_one a t m k ht

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def taylorInitialRequest (N k : ℕ) : ℕ := k + N * (N + 3)

theorem taylorInitialRequest_step (n k : ℕ) :
    taylorInitialRequest n (k + n + 2) ≤ taylorInitialRequest (n + 1) k := by
  unfold taylorInitialRequest
  nlinarith

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorRemainderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem iteratedDerivWithin_Icc_eq_of_contDiffAt {f : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (hf : ContDiffAt ℝ ∞ f t) (ht : t ∈ Icc a b) (k : ℕ) :
    iteratedDerivWithin k f (Icc a b) t = iteratedDeriv k f t := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hab)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)) ht]

theorem zero_jets_remainder_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ f t) (N : ℕ)
    (hzero : ∀ k < N, iteratedDeriv k f a = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc a b, |iteratedDeriv N f t| ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) : |f t| ≤ C * (t - a)^N := by
  cases N with
  | zero => simpa only [iteratedDeriv_zero, pow_zero, mul_one] using hbound t ht
  | succ n =>
    rcases eq_or_lt_of_le hab with hab | hab
    · subst b
      have hta : t = a := le_antisymm ht.2 ht.1
      subst t
      have hfa : f a = 0 := hzero 0 (by omega)
      simp [hfa]
    have hwithin (j : ℕ) (s : ℝ) (hs : s ∈ Icc a b) :
        iteratedDerivWithin j f (Icc a b) s = iteratedDeriv j f s :=
      iteratedDerivWithin_Icc_eq_of_contDiffAt hab (hf s hs) hs j
    have hTaylor : taylorWithinEval f n (Icc a b) a t = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hwithin j a ⟨le_rfl, hab.le⟩, hzero j (Finset.mem_range.mp hj)]
      simp
    have hdiff : ContDiffOn ℝ (n + 1) f (Icc a b) :=
      fun s hs => ((hf s hs).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
    have hrem := taylor_mean_remainder_bound hab.le hdiff ht
      (fun s hs => by rw [hwithin (n + 1) s hs, Real.norm_eq_abs]; exact hbound s hs)
    rw [hTaylor, sub_zero, Real.norm_eq_abs] at hrem
    apply hrem.trans
    have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)
    exact div_le_self (mul_nonneg hC (pow_nonneg (sub_nonneg.mpr ht.1) _)) hfac

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def taylorStripJetOrder (N : ℕ) : ℕ := max 3 (N + 2)

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorPulse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_pulse_width_threshold {epsilon delta : ℝ} (he : 0 < epsilon)
    (_hd : 0 < delta) :
    ∃ tau0 : ℕ, 0 < tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      0 < tau ∧ 2 * delta / (tau : ℝ) ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * delta / epsilon)
  refine ⟨max 1 n, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro tau htau
  have ht : 0 < tau := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans htau)
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr ht
  have hnreal : (n : ℝ) ≤ (tau : ℝ) := by exact_mod_cast (le_max_right 1 n).trans htau
  have hn' : 2 * delta < (n : ℝ) * epsilon := (div_lt_iff₀ he).mp hn
  refine ⟨ht, (div_le_iff₀ htr).mpr ?_⟩
  nlinarith

theorem pulse_time_power_bound {delta C t : ℝ} {tau N : ℕ}
    (_hd : 0 < delta) (hdhalf : delta ≤ 1 / 2) (htau : 0 < tau) (hC : 0 ≤ C)
    (ht : t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ))) :
    C * (t - (-delta / (tau : ℝ)))^N ≤ C / (tau : ℝ)^N := by
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr htau
  have hleft : 0 ≤ t - (-delta / (tau : ℝ)) := sub_nonneg.mpr ht.1
  have hright : t - (-delta / (tau : ℝ)) ≤ 1 / (tau : ℝ) := by
    have hw : t - (-delta / (tau : ℝ)) ≤ 2 * delta / (tau : ℝ) := by
      have hs := sub_le_sub_right ht.2 (-delta / (tau : ℝ))
      convert hs using 1 <;> first | rfl | ring
    exact hw.trans ((div_le_div_iff_of_pos_right htr).mpr (by linarith))
  have hp := pow_le_pow_left₀ hleft hright N
  have hm := mul_le_mul_of_nonneg_left hp hC
  simpa only [div_pow, one_pow, mul_one_div] using hm

end SmoothLocal.Taylor

end

end OAI
end


