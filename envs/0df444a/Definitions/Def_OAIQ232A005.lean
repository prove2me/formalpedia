-- Prove2me | Definitions.Def_OAIQ232A005
-- name    : OAIQ232A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:41:18.681273+00:00
-- url     : https://prove2.me/theorems/3bbd6706-4ee2-4622-84f2-3f7f689ef518
-- title:
--   Definitions bundle OAIQ232A005 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 38 definitions, 8 instances and 86 theorems. The definitions and types are `OAI.WeakMTWTransport.bilinearAbsorptionDualNormedAddCommGroup`, `OAI.WeakMTWTransport.bilinearAbsorptionDualNormedSpace`, `OAI.WeakMTWTransport.bilinearCompactDualGroup`, `OAI.WeakMTWTransport.bilinearCompactDualSpace`, `OAI.WeakMTWTransport.bilinearCompactGroup`, `OAI.WeakMTWTransport.bilinearCompactSpace`, `OAI.WeakMTWTransport.bilinearMatrix`, `OAI.WeakMTWTransport.bilinearOperator`, `OAI.WeakMTWTransport.boundedModifiedDatum`, `OAI.WeakMTWTransport.centerDetDualGroup`, `OAI.WeakMTWTransport.centerDetDualSpace`, `OAI.WeakMTWTransport.centerGamma`, `OAI.WeakMTWTransport.centerTemplate`, `OAI.WeakMTWTransport.covectorSquare`, `OAI.WeakMTWTransport.dualCompactGroup`, `OAI.WeakMTWTransport.dualCompactSpace`, `OAI.WeakMTWTransport.gainDualGroup`, `OAI.WeakMTWTransport.gainDualSpace`, `OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealIdTangentSpaceModelModelWithCornersSelf`, `OAI.WeakMTWTransport.lowerGapScale`, `OAI.WeakMTWTransport.outerJ`, `OAI.WeakMTWTransport.outerPrimitive`, `OAI.WeakMTWTransport.outerProfile`, `OAI.WeakMTWTransport.outerTemplate`, `OAI.WeakMTWTransport.outerVelocity`, `OAI.WeakMTWTransport.outerW`, `OAI.WeakMTWTransport.positiveCompactDualGroup`, `OAI.WeakMTWTransport.positiveCompactDualSpace`, `OAI.WeakMTWTransport.pullBilinear`, `OAI.WeakMTWTransport.restrictedTransform`, `OAI.WeakMTWTransport.reverseNormalizedPair`, `OAI.WeakMTWTransport.secondJetPullback`, `OAI.WeakMTWTransport.spectralShear`, `OAI.WeakMTWTransport.templateEps`, `OAI.WeakMTWTransport.twoMountain`, `OAI.WeakMTWTransport.upperGapScale`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_ScalarFamily`, `BiholderTransport_Calculus_SecondDerivativeLinearSandwich`, `BiholderTransport_Calculus_SecondDerivativeSlice`, `BiholderTransport_Contact_GlobalSupport`, `BiholderTransport_Contact_MiddleExclusion`, `BiholderTransport_Convexity_ShortEnvelopeJetTest`, `BiholderTransport_Coordinates_ChartLipschitz`, `BiholderTransport_Duality_DualCompact`, `BiholderTransport_Geodesics_MinimizingChartParameters`, `BiholderTransport_LinearAlgebra_BilinearAbsorption`, `BiholderTransport_LinearAlgebra_BilinearCompact`, `BiholderTransport_LinearAlgebra_BilinearGainLimit`, `BiholderTransport_LinearAlgebra_BilinearMatrix`, `BiholderTransport_LinearAlgebra_CompactLocalPositiveBounds`, `BiholderTransport_LinearAlgebra_EigenOrder`, `BiholderTransport_LinearAlgebra_LowerTaylor`, `BiholderTransport_LinearAlgebra_OperatorBounds`, `BiholderTransport_LinearAlgebra_PositiveDetCompact`, `BiholderTransport_LinearAlgebra_ShearConvexity`, `BiholderTransport_Oscillation_SectionOscillation`, `BiholderTransport_Regularity_ActualScaleSmallness`, `BiholderTransport_Regularity_CenterDetCompact`, `BiholderTransport_Regularity_ContDiffParametricQuadratic`, `BiholderTransport_Regularity_CriticalChain`, `BiholderTransport_Regularity_InteriorMaximum`, `BiholderTransport_Regularity_OuterTemplate`, `BiholderTransport_Regularity_RestrictedTransform`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A011` and `OAIQ232A012`.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport

section
-- module Solutions.OAIQ232_BH.Compat
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
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma scalar_family_hasDeriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (p:ℝ×ℝ) :
    HasDerivAt (fun s=>Φ (p.1,s)) (fderiv ℝ Φ p (0,1)) p.2 := by
  have H := (hΦ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact H

lemma scalar_family_derivable {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (p:ℝ×ℝ) :
    HasDerivAt (fun s=>Φ (p.1,s)) (deriv (fun s=>Φ (p.1,s)) p.2) p.2 :=
  (scalar_family_hasDeriv hΦ p).differentiableAt.hasDerivAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EigenOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def bilinearOperator (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

@[simp] lemma bilinearOperator_inner (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    inner ℝ (bilinearOperator B v) w=B v w :=
  InnerProductSpace.toDual_symm_apply

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeJetTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def secondJetPullback (j : F →L[ℝ] ℝ) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (m : E →L[ℝ] F) (r : E →L[ℝ] E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ).flip m).comp (h.comp m)+
    (ContinuousLinearMap.compL ℝ E F ℝ j).comp r

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondDerivativeLinearSandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma second_derivative_linear_sandwich {f : F → G} {a : E}
    (L : E →L[ℝ] F) (K : G →L[ℝ] H) (hf : ContDiffAt ℝ 2 f (L a)) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => K (f (L x)))) a u v =
      K (fderiv ℝ (fderiv ℝ f) (L a) (L u) (L v)) := by
  have heq : fderiv ℝ (fun x => K (f (L x))) =ᶠ[𝓝 a]
      fun x => K.comp ((fderiv ℝ f (L x)).comp L) := by
    filter_upwards [L.continuous.continuousAt.eventually (hf.eventually (by norm_num))] with x hx
    exact (K.hasFDerivAt.comp x ((hx.differentiableAt (by norm_num)).hasFDerivAt.comp x
      L.hasFDerivAt)).fderiv
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD := (hasFDerivAt_const K a).clm_comp
    ((hdd.hasFDerivAt.comp a L.hasFDerivAt).clm_comp (hasFDerivAt_const L a))
  have h := congrArg (fun A : E →L[ℝ] E →L[ℝ] H => A u v)
    ((hD.congr_of_eventuallyEq heq).fderiv)
  simpa only [comp_apply,compL_apply,flip_apply,add_apply,zero_apply,map_zero,zero_add,add_zero] using h

end WeakMTWTransport

end



noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma second_derivative_half_norm_sq {g : E → F} {a v : E}
    (hg : ContDiffAt ℝ 2 g a) :
    fderiv ℝ (fderiv ℝ (fun x => ‖g x‖^2/2)) a v v =
      ‖fderiv ℝ g a v‖^2 + inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v) := by
  let G : E → E →L[ℝ] ℝ := fun x => (innerSL ℝ (g x)).comp (fderiv ℝ g x)
  have hdg := hg.differentiableAt (by norm_num)
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG := ((innerSL ℝ).hasFDerivAt.comp a hdg.hasFDerivAt).clm_comp hddg.hasFDerivAt
  have heq : fderiv ℝ (fun x => ‖g x‖^2/2) =ᶠ[𝓝 a] G := by
    filter_upwards [hg.eventually (by norm_num : (2:ℕ∞ω)≠∞)] with x hx
    have hd0 := ((hx.differentiableAt (by norm_num)).hasFDerivAt.norm_sq).const_smul (1/2:ℝ)
    have hd := hd0.fderiv
    have hfun : (fun z => ‖g z‖^2/2)=(fun z => (1/2:ℝ) • ‖g z‖^2) := by
      funext z; simp only [smul_eq_mul] <;> ring
    rw [hfun]
    change fderiv ℝ ((1/2:ℝ) • fun z => ‖g z‖^2) x=G x
    rw [hd]
    ext w
    simp only [G,comp_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
    ring
  have hD := (hG.congr_of_eventuallyEq heq).fderiv
  rw [hD]
  simp only [comp_apply,compL_apply,add_apply,flip_apply]
  change inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v)+inner ℝ (fderiv ℝ g a v) (fderiv ℝ g a v)=_
  rw [real_inner_self_eq_norm_sq,add_comm]

lemma third_derivative_swap_outer {f : E → ℝ} {a u v w : E}
    (hf : ContDiffAt ℝ 3 f a) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a v u w := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num) |>.eq u v)

lemma third_derivative_swap_inner {f : E → ℝ} {a u v w : E}
    (hf : ContDiffAt ℝ 3 f a) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) a u w v := by
  let H := fderiv ℝ (fderiv ℝ f)
  have hH := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvw := (hH.hasFDerivAt.clm_apply (hasFDerivAt_const v a)).clm_apply
    (hasFDerivAt_const w a)
  have hwv := (hH.hasFDerivAt.clm_apply (hasFDerivAt_const w a)).clm_apply
    (hasFDerivAt_const v a)
  have heq : (fun x => H x v w)=ᶠ[𝓝 a] (fun x => H x w v) := by
    filter_upwards [hf.eventually (by norm_num : (3:ℕ∞ω)≠∞)] with x hx
    exact hx.isSymmSndFDerivAt (by norm_num) |>.eq v w
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L u)
    ((hvw.congr_of_eventuallyEq heq.symm).unique hwv)
  simpa only [comp_apply,flip_apply,add_apply,zero_apply,map_zero,zero_add,add_zero] using hh

lemma eikonal_third_derivative {B : E×F → ℝ} {g : E → F} {a v : E}
    (hB : ContDiffAt ℝ 3 B (a,0)) (hg : ContDiffAt ℝ 2 g a)
    (heik : (fun x => B (x,0)) =ᶠ[𝓝 a] (fun x => ‖g x‖^2/2))
    (hgrad : ∀ᶠ x in 𝓝 a, ∀ w : F,
      fderiv ℝ B (x,0) (0,w)=inner ℝ (g x) w) :
    fderiv ℝ (fderiv ℝ B) (a,0) (v,0) (v,0) =
      ‖fderiv ℝ g a v‖^2+
        fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,0) (0,g a) (v,0) (v,0) := by
  let L := ContinuousLinearMap.inl ℝ E F
  have hL : L a=(a,0) := rfl
  have hsource := second_derivative_linear_sandwich L (ContinuousLinearMap.id ℝ ℝ)
    (show ContDiffAt ℝ 2 B (L a) from hB.of_le (by norm_num)) v v
  have hnorm := congrArg (fun D : E →L[ℝ] E →L[ℝ] ℝ => D v v)
    (heik.fderiv (𝕜 := ℝ)).fderiv_eq
  have hs : fderiv ℝ (fderiv ℝ B) (a,0) (v,0) (v,0)=
      ‖fderiv ℝ g a v‖^2+inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v) := by
    have hsource' : fderiv ℝ (fderiv ℝ (fun x => B (x,0))) a v v =
        fderiv ℝ (fderiv ℝ B) (a,0) (v,0) (v,0) := hsource
    rw [←hsource']
    exact hnorm.trans (second_derivative_half_norm_sq hg)
  have hpartial : (fun x => fderiv ℝ B (x,0) (0,g a)) =ᶠ[𝓝 a]
      fun x => inner ℝ (g a) (g x) := by
    filter_upwards [hgrad] with x hx
    rw [hx,real_inner_comm]
  have hp2 := congrArg (fun D : E →L[ℝ] E →L[ℝ] ℝ => D v v)
    (hpartial.fderiv (𝕜 := ℝ)).fderiv_eq
  have hleft := second_derivative_linear_sandwich L
    (ContinuousLinearMap.apply ℝ ℝ ((0:E),g a))
    (show ContDiffAt ℝ 2 (fderiv ℝ B) (L a) from hB.fderiv_right (by norm_num)) v v
  have hright := second_derivative_linear_sandwich (ContinuousLinearMap.id ℝ E)
    (innerSL ℝ (g a)) hg v v
  have htr : inner ℝ (g a) (fderiv ℝ (fderiv ℝ g) a v v)=
      fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,0) (v,0) (v,0) (0,g a) := by
    exact hright.symm.trans (hp2.symm.trans hleft)
  rw [hs,htr]
  congr 1
  rw [third_derivative_swap_inner hB,third_derivative_swap_outer hB]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondDerivativeSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_derivative_source_slice {B : E×F → ℝ} {a : E} {b : F}
    (hB : ContDiffAt ℝ 2 B (a,b)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun x => B (x,b))) a v w =
      fderiv ℝ (fderiv ℝ B) (a,b) (v,0) (w,0) := by
  let L : E →L[ℝ] E×F := inl ℝ E F
  let C : E×F → ℝ := fun z => B (z+(0,b))
  have hC : ContDiffAt ℝ 2 C (L a) := by
    have hB' : ContDiffAt ℝ 2 B (L a+(0,b)) := by
      simpa only [L,inl_apply,Prod.mk_add_mk,add_zero,zero_add] using hB
    exact hB'.comp (L a) (contDiffAt_id.add contDiffAt_const)
  have h := second_derivative_linear_sandwich L (ContinuousLinearMap.id ℝ ℝ) hC v w
  have heq : fderiv ℝ C =ᶠ[𝓝 (a,0)] fun z => fderiv ℝ B (z+(0,b)) := by
    filter_upwards [((continuousAt_id.add_const (0,b)).eventually
      (show ∀ᶠ z in 𝓝 ((a,0)+(0,b)), ContDiffAt ℝ 2 B z from by
        simpa only [Prod.mk_add_mk,add_zero,zero_add] using hB.eventually (by norm_num)))] with z hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (0,b))).fderiv
  have hD := ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD' : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) (a,b)) ((a,0)+(0,b)) := by
    simpa using hD
  have hDc := hD'.comp (a,0) ((hasFDerivAt_id (a,(0:F))).add_const (0,b))
  have hDD := (hDc.congr_of_eventuallyEq heq).fderiv
  have hh : fderiv ℝ (fderiv ℝ C) (a,0)=fderiv ℝ (fderiv ℝ B) (a,b) := by
    simpa only [comp_id] using hDD
  have hh' : fderiv ℝ (fderiv ℝ (fun x => B (x,b))) a v w =
      fderiv ℝ (fderiv ℝ C) (a,0) (v,0) (w,0) := by
    simpa only [id_apply,C,L,inl_apply,Prod.mk_add_mk,add_zero,zero_add] using h
  exact hh'.trans (congrArg (fun K : E×F →L[ℝ] E×F →L[ℝ] ℝ => K (v,0) (w,0)) hh)

lemma hasDerivAt_source_hessian_line {B : E×F → ℝ} {a v : E} {b w : F} {t : ℝ}
    (hB : ContDiffAt ℝ 3 B (a,b)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ
      (fun x => B (x,b+(s-t) • w))) a v v)
      (fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,b) (0,w) (v,0) (v,0)) t := by
  let q : ℝ → E×F := fun s => (a,b+(s-t) • w)
  have hq : HasDerivAt q (0,w) t := by
    simpa only [q,one_smul,id_eq] using (hasDerivAt_const t a).prodMk
      (((hasDerivAt_id t).sub_const t).smul_const w |>.const_add b)
  have hqt : q t=(a,b) := by simp [q]
  have hH := ((hB.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH' : HasFDerivAt (fderiv ℝ (fderiv ℝ B))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (a,b)) (q t) := hqt.symm ▸ hH.hasFDerivAt
  have hD := hH'.comp_hasDerivAt (f := q) (l := fderiv ℝ (fderiv ℝ B)) t hq
  have hD' := (hD.clm_apply (hasDerivAt_const t (v,(0:F)))).clm_apply
    (hasDerivAt_const t (v,(0:F)))
  have heq : (fun s : ℝ => fderiv ℝ (fderiv ℝ
      (fun x => B (x,b+(s-t) • w))) a v v) =ᶠ[𝓝 t]
      fun s => fderiv ℝ (fderiv ℝ B) (q s) (v,0) (v,0) := by
    filter_upwards [hq.continuousAt.eventually
      (show ∀ᶠ z in 𝓝 (q t), ContDiffAt ℝ 3 B z from by
        rw [hqt]; exact hB.eventually (by norm_num))] with s hs
    exact second_derivative_source_slice (hs.of_le (by norm_num)) v v
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  simpa only [Function.comp_apply,zero_add,add_zero,map_zero] using hD'

end WeakMTWTransport

end



noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma second_derivative_target_slice {B : E×F → ℝ} {a : E} {b : F}
    (hB : ContDiffAt ℝ 2 B (a,b)) (v w : F) :
    fderiv ℝ (fderiv ℝ (fun y => B (a,y))) b v w =
      fderiv ℝ (fderiv ℝ B) (a,b) (0,v) (0,w) := by
  let L : F →L[ℝ] E×F := inr ℝ E F
  let C : E×F → ℝ := fun z => B (z+(a,0))
  have hC : ContDiffAt ℝ 2 C (L b) := by
    have hB' : ContDiffAt ℝ 2 B (L b+(a,0)) := by
      simpa only [L,inr_apply,Prod.mk_add_mk,add_zero,zero_add] using hB
    exact hB'.comp (L b) (contDiffAt_id.add contDiffAt_const)
  have h := second_derivative_linear_sandwich L (ContinuousLinearMap.id ℝ ℝ) hC v w
  have heq : fderiv ℝ C =ᶠ[𝓝 (0,b)] fun z => fderiv ℝ B (z+(a,0)) := by
    filter_upwards [((continuousAt_id.add_const (a,0)).eventually
      (show ∀ᶠ z in 𝓝 ((0,b)+(a,0)), ContDiffAt ℝ 2 B z from by
        simpa only [Prod.mk_add_mk,add_zero,zero_add] using hB.eventually (by norm_num)))] with z hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (a,0))).fderiv
  have hD := ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD' : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) (a,b)) ((0,b)+(a,0)) := by
    simpa using hD
  have hDc := hD'.comp ((0:E),b) ((hasFDerivAt_id ((0:E),b)).add_const (a,0))
  have hDD := (hDc.congr_of_eventuallyEq heq).fderiv
  have hh : fderiv ℝ (fderiv ℝ C) (0,b)=fderiv ℝ (fderiv ℝ B) (a,b) := by
    simpa only [comp_id] using hDD
  have hh' : fderiv ℝ (fderiv ℝ (fun y => B (a,y))) b v w =
      fderiv ℝ (fderiv ℝ C) (0,b) (0,v) (0,w) := by
    simpa only [id_apply,C,L,inr_apply,Prod.mk_add_mk,add_zero,zero_add] using h
  exact hh'.trans (congrArg (fun K : E×F →L[ℝ] E×F →L[ℝ] ℝ => K (0,v) (0,w)) hh)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def twoMountain (x y₀ y₁ z : M) : ℝ :=
  max (cost x y₀-cost z y₀) (cost x y₁-cost z y₁)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_MiddleExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory
open scoped Topology Interval ContDiff

def templateEps : ℝ := (2:ℝ)^(-10:ℤ)

def centerGamma : ℝ := 8*Real.log 2047

def centerTemplate (s : ℝ) : ℝ :=
  1-2/(1+Real.exp (-centerGamma*(s-5/8)))

def outerVelocity (M0 K eta s : ℝ) : ℝ :=
  let kappa := K+1
  let A := M0+3
  let L := 128*A*kappa
  let h0 := 1/(128*kappa)
  (L-kappa*s)*Real.smoothTransition ((s+3*eta)/eta)*
    (1-Real.smoothTransition ((s-h0)/h0))

def outerPrimitive (M0 K eta s : ℝ) : ℝ :=
  1+templateEps/2+∫ q in (0:ℝ)..s,outerVelocity M0 K eta q

def outerTemplate (M0 K eta s : ℝ) : ℝ :=
  outerPrimitive M0 K eta s*
    (1-Real.smoothTransition ((s-(1-eta))/eta))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ChartLipschitz
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance instNormedAddCommGroupContinuousLinearMapRealIdTangentSpaceModelModelWithCornersSelf (y : Model n) (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedAddCommGroup

end ChartLipschitz
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_DualCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section DualCompact
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance dualCompactGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance dualCompactSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end DualCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MinimizingChartParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma tangent_chart_symm_trivialization {a : M} {q : Model n×Model n}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm q=
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm q.1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hq
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearAbsorption
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance bilinearAbsorptionDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance bilinearAbsorptionDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

def covectorSquare (p:E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  p.smulRight p

end BilinearAbsorption
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance bilinearCompactDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance bilinearCompactDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance bilinearCompactGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance bilinearCompactSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

end BilinearCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace WeakMTWTransport
section BilinearMatrix
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def bilinearMatrix (B:E →L[ℝ] E →L[ℝ] ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (bilinearOperator B).toLinearMap.toMatrix (stdOrthonormalBasis ℝ E).toBasis
    (stdOrthonormalBasis ℝ E).toBasis

end BilinearMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterDetCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section CenterDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance centerDetDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance centerDetDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end CenterDetCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearGainLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearGainLimit
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance gainDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gainDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end BilinearGainLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContDiffParametricQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma compact_eventually_uniform_radius_bound {A T : Type*}
    [TopologicalSpace A] [TopologicalSpace T] {K : Set A} (hK : IsCompact K)
    {t : T} {P : ℝ → ℝ → T → A → Prop}
    (hmono : ∀ {r R b B : ℝ}, 0 < r → r≤R → b≤B → ∀ s a, P R b s a → P r B s a)
    (hlocal : ∀ a∈K, ∃ r>0, ∃ b>0, ∀ᶠ q : T×A in 𝓝 (t,a), P r b q.1 q.2) :
    ∃ r>0, ∃ b>0, ∀ᶠ s in 𝓝 t, ∀ a∈K, P r b s a := by
  apply hK.induction_on
    (p := fun J => ∃ r>0, ∃ b>0, ∀ᶠ s in 𝓝 t, ∀ a∈J, P r b s a)
  · exact ⟨1,by norm_num,1,by norm_num,Filter.Eventually.of_forall (by simp)⟩
  · intro J L hJL hL
    obtain ⟨r,hr,b,hb,H⟩ := hL
    refine ⟨r,hr,b,hb,?_⟩
    filter_upwards [H] with s hs
    exact fun a ha => hs a (hJL ha)
  · intro J L hJ hL
    obtain ⟨r,hr,b,hb,H⟩ := hJ
    obtain ⟨R,hR,B,hB,G⟩ := hL
    refine ⟨min r R,lt_min hr hR,max b B,lt_max_of_lt_left hb,?_⟩
    filter_upwards [H,G] with s hs gs
    intro a ha
    rcases ha with ha|ha
    · exact hmono (lt_min hr hR) (min_le_left _ _) (le_max_left _ _) s a (hs a ha)
    · exact hmono (lt_min hr hR) (min_le_right _ _) (le_max_right _ _) s a (gs a ha)
  · intro a ha
    obtain ⟨r,hr,b,hb,H⟩ := hlocal a ha
    obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp H
    refine ⟨V,mem_nhdsWithin_of_mem_nhds hV,r,hr,b,hb,?_⟩
    filter_upwards [hU] with s hs
    intro a ha
    exact hUV (show (s,a)∈U×ˢV from ⟨hs,ha⟩)

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactLocalPositiveBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma compact_local_positive_bounds {A : Type*} [TopologicalSpace A]
    {K : Set A} (hK : IsCompact K) {P : ℝ → ℝ → A → Prop}
    (hmono : ∀ {r R b B : ℝ}, 0 < r → r≤R → b≤B → ∀ a, P R b a → P r B a)
    (hlocal : ∀ a∈K, ∃ r b : ℝ, 0 < r ∧ 0<b ∧ ∀ᶠ z in 𝓝 a, P r b z) :
    ∃ r b : ℝ, 0 < r ∧ 0<b ∧ ∀ a∈K, P r b a := by
  obtain ⟨r,hr,b,hb,H⟩ := compact_eventually_uniform_radius_bound
    (T := Unit) (t := ()) (P := fun r b (_ : Unit) a => P r b a) hK
    (fun hr hR hB _ a ha => hmono hr hR hB a ha) (by
      intro a ha
      obtain ⟨r,b,hr,hb,H⟩ := hlocal a ha
      exact ⟨r,hr,b,hb,continuousAt_snd.eventually H⟩)
  exact ⟨r,b,hr,hb,H.self_of_nhds⟩

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LowerTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pullBilinear (B : F →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)

@[simp] lemma pullBilinear_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (A : E →L[ℝ] F)
    (u v : E) : pullBilinear B A u v=B (A u) (A v) := rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_OperatorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology

namespace WeakMTWTransport
section OperatorBounds
variable {A E F : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma eventually_injective_operator_bounds {f : A → E →L[ℝ] F} {a : A}
    (hf : ContinuousAt f a) (hi : Function.Injective (f a)) :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ᶠ b in 𝓝 a, ∀ v,
      c*‖v‖≤‖f b v‖ ∧ ‖f b v‖≤C*‖v‖ := by
  obtain ⟨K,hK,hKa⟩ := (f a).injective_iff_antilipschitz.mp hi
  have hKr : 0<(K:ℝ) := hK
  let c : ℝ := (2*(K:ℝ))⁻¹
  have hc : 0 < c := inv_pos.mpr (mul_pos (by norm_num) hKr)
  have he : ∀ᶠ b in 𝓝 a, ‖f b-f a‖ < c :=
    (hf.sub_const (f a)).norm.eventually (gt_mem_nhds (by simpa using hc))
  refine ⟨c,‖f a‖+c,hc,by positivity,?_⟩
  filter_upwards [he] with b hb
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz (f a) hKa v
  have H' : (K:ℝ)⁻¹*‖v‖≤‖f a v‖ := by
    rw [inv_mul_le_iff₀ hKr]
    exact H
  have hdiff : ‖f b v-f a v‖ ≤ c*‖v‖ :=
    ((f b-f a).le_opNorm v).trans (mul_le_mul_of_nonneg_right hb.le (norm_nonneg v))
  have htri : ‖f a v‖≤‖f b v‖+‖f b v-f a v‖ := by
    have ht := norm_add_le (f b v) (f a v-f b v)
    rw [←add_sub_assoc,add_sub_cancel_left,norm_sub_rev] at ht
    exact ht
  have hcn : (K:ℝ)⁻¹=2*c := by dsimp [c]; field_simp
  constructor
  · rw [hcn] at H'
    nlinarith
  · calc
      ‖f b v‖≤‖f a v‖+‖f b v-f a v‖ := by
        have ht := norm_add_le (f a v) (f b v-f a v)
        rwa [←add_sub_assoc,add_sub_cancel_left] at ht
      _ ≤ ‖f a‖*‖v‖+c*‖v‖ := add_le_add ((f a).le_opNorm v) hdiff
      _ = (‖f a‖+c)*‖v‖ := by ring

end OperatorBounds
end WeakMTWTransport

end

end

section

noncomputable section
open ContinuousLinearMap

namespace WeakMTWTransport
section OperatorTransfer
variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma operator_bounds_through_charts (U : E →L[ℝ] H) (Ui : H →L[ℝ] E)
    (V : F →L[ℝ] H) (Vi : H →L[ℝ] F) (A : H →L[ℝ] H) (P : E →L[ℝ] F)
    (hU : ∀ v, Ui (U v)=v) (hV : ∀ w, Vi (V w)=w)
    (hA : ∀ v, A (U v)=V (P v))
    {c C CU DU CV DV : ℝ} (hc : 0 < c) (hC : 0<C)
    (hCU : 0<CU) (hDU : 0<DU) (hCV : 0<CV) (hDV : 0<DV)
    (hUb : ‖U‖≤CU) (hUib : ‖Ui‖≤DU) (hVb : ‖V‖≤CV) (hVib : ‖Vi‖≤DV)
    (hAb : ∀ w, c*‖w‖≤‖A w‖ ∧ ‖A w‖≤C*‖w‖) :
    ∀ v, c/(DU*CV)*‖v‖≤‖P v‖ ∧ ‖P v‖≤DV*C*CU*‖v‖ := by
  intro v
  have hu : ‖v‖≤DU*‖U v‖ := by
    calc
      ‖v‖=‖Ui (U v)‖ := by rw [hU]
      _ ≤ ‖Ui‖*‖U v‖ := Ui.le_opNorm _
      _ ≤ DU*‖U v‖ := mul_le_mul_of_nonneg_right hUib (norm_nonneg _)
  have hv : ‖P v‖≤DV*‖V (P v)‖ := by
    calc
      ‖P v‖=‖Vi (V (P v))‖ := by rw [hV]
      _ ≤ ‖Vi‖*‖V (P v)‖ := Vi.le_opNorm _
      _ ≤ DV*‖V (P v)‖ := mul_le_mul_of_nonneg_right hVib (norm_nonneg _)
  have hvu : ‖V (P v)‖≤CV*‖P v‖ :=
    (V.le_opNorm _).trans (mul_le_mul_of_nonneg_right hVb (norm_nonneg _))
  have huu : ‖U v‖≤CU*‖v‖ :=
    (U.le_opNorm _).trans (mul_le_mul hUb le_rfl (norm_nonneg _) hCU.le)
  have hlow : c*‖v‖≤(DU*CV)*‖P v‖ := by
    calc
      c*‖v‖ ≤ c*(DU*‖U v‖) := mul_le_mul_of_nonneg_left hu hc.le
      _ = DU*(c*‖U v‖) := by ring
      _ ≤ DU*‖A (U v)‖ := mul_le_mul_of_nonneg_left (hAb _).1 hDU.le
      _ = DU*‖V (P v)‖ := by rw [hA]
      _ ≤ DU*(CV*‖P v‖) := mul_le_mul_of_nonneg_left hvu hDU.le
      _ = _ := by ring
  refine ⟨?_,?_⟩
  · rw [div_mul_eq_mul_div,div_le_iff₀ (mul_pos hDU hCV)]
    nlinarith [hlow]
  · calc
      ‖P v‖ ≤ DV*‖V (P v)‖ := hv
      _ = DV*‖A (U v)‖ := by rw [hA]
      _ ≤ DV*(C*‖U v‖) := mul_le_mul_of_nonneg_left (hAb _).2 hDV.le
      _ ≤ DV*(C*(CU*‖v‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left huu hC.le) hDV.le
      _ = _ := by ring

end OperatorTransfer
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveDetCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section PositiveDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance positiveCompactDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance positiveCompactDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end PositiveDetCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearConvexity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def spectralShear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (t / inner ℝ p q) • (innerSL ℝ q).smulRight q

end ShearConvexity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

def reverseNormalizedPair (x0 : M) (uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)) :
    (M →ᵇ ℝ) × (M →ᵇ ℝ) :=
  (uv.2 + BoundedContinuousFunction.const M (-uv.2 x0),
    uv.1 + BoundedContinuousFunction.const M (uv.2 x0))

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualScaleSmallness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

def lowerGapScale (A J:ℝ):ℝ := Real.exp (-(A+2*J/3))
def upperGapScale (A J:ℝ):ℝ := Real.exp (-(A+J/3))

end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CriticalChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section CriticalChain
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_at_critical {f : F → ℝ} {g : E → F} {p : E}
    (hf : ContDiffAt ℝ 2 f (g p)) (hg : ContDiffAt ℝ 2 g p)
    (hzero : fderiv ℝ f (g p)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) p v w=
      fderiv ℝ (fderiv ℝ f) (g p) (fderiv ℝ g p v) (fderiv ℝ g p w) := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hn : ∀ᶠ a in 𝓝 p, DifferentiableAt ℝ g a ∧ DifferentiableAt ℝ f (g a) := by
    have hnG := (hg.of_le (m := 1) (by norm_num)).eventually (by norm_num)
    have hnF := hg.continuousAt.eventually ((hf.of_le (m := 1) (by norm_num)).eventually (by norm_num))
    filter_upwards [hnG,hnF] with a ha hb
    exact ⟨ha.differentiableAt (by norm_num),hb.differentiableAt (by norm_num)⟩
  have heq : fderiv ℝ (f ∘ g) =ᶠ[𝓝 p]
      (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) :=
    hn.mono (fun a ha => fderiv_comp a ha.2 ha.1)
  have hD := (hdf.hasFDerivAt.comp p (hg.differentiableAt (by norm_num)).hasFDerivAt).clm_comp hdg.hasFDerivAt
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) (heq.fderiv_eq.trans hD.fderiv)
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, Function.comp_apply,
    hzero, ContinuousLinearMap.zero_comp,_root_.zero_apply,zero_add] using H

end CriticalChain
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_InteriorMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def boundedModifiedDatum (v : M → ℝ) (hv : Continuous v) (a D : ℝ)
    (B : ℝ → ℝ) (hB : Continuous B) (b : ℝ) : M →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨v,hv⟩ + b •
    BoundedContinuousFunction.mkOfCompact ⟨fun y => B ((v y-a)/D),
      hB.comp ((hv.sub continuous_const).div_const D)⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

def outerW (K M η s:ℝ):ℝ :=
  (128*(M+3)*(K+1)-(K+1)*s)*Real.smoothTransition ((s+3*η)/η)*
    (1-Real.smoothTransition ((s-1/(128*(K+1)))/(1/(128*(K+1)))))

def outerJ (K M η s:ℝ):ℝ := 1+(1/2048:ℝ)+∫ q in (0:ℝ)..s,outerW K M η q

def outerProfile (K M η s:ℝ):ℝ :=
  outerJ K M η s*(1-Real.smoothTransition ((s-(1-η))/η))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_RestrictedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
section RestrictedTransform
variable {M : Type*} [MetricSpace M] [CompactSpace M]

def restrictedTransform (v : M → ℝ) (S : Set M) (x : M) : ℝ :=
  sSup ((fun y => -cost x y-v y) '' S)

end RestrictedTransform
end WeakMTWTransport

end

end

end

end OAI
end


