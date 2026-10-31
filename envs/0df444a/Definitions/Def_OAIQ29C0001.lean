-- Prove2me | Definitions.Def_OAIQ29C0001
-- name    : OAIQ29C0001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:42:23.769266+00:00
-- url     : https://prove2.me/theorems/2f5e57f3-4a0a-4075-b119-a8424a2e8524
-- title:
--   Definitions bundle OAIQ29C0001 of the split of OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 322 declarations of OpenAI's Lean: 111 definitions, 1 inductive type or structure, 14 instances and 196 theorems. The definitions and types are `OAI.CAT0Fillings.ChordAverage.average`, `OAI.CAT0Fillings.ChordTransform.kernel`, `OAI.CAT0Fillings.ChordTransform.transform`, `OAI.CAT0Fillings.ClosedCalculus.absApprox`, `OAI.CAT0Fillings.ClosedCalculus.absApproxDeriv`, `OAI.CAT0Fillings.ClosedCalculus.binaryDerivative`, `OAI.CAT0Fillings.ClosedCalculus.levelApprox`, `OAI.CAT0Fillings.ClosedCalculus.levelApproxDeriv`, `OAI.CAT0Fillings.ClosedCalculus.lowerCut`, `OAI.CAT0Fillings.ClosedCalculus.mulLp`, `OAI.CAT0Fillings.ClosedCalculus.scalarAverage`, `OAI.CAT0Fillings.ClosedCalculus.scalarAverageDeriv`, `OAI.CAT0Fillings.ClosedCalculus.truncatedPower`, `OAI.CAT0Fillings.ClosedCalculus.truncatedPowerSlope`, `OAI.CAT0Fillings.ClosedCalculus.upperCut`, `OAI.CAT0Fillings.ClosedCylinder`, `OAI.CAT0Fillings.Conformal.averageProfile`, `OAI.CAT0Fillings.Conformal.averageProfileDeriv`, `OAI.CAT0Fillings.Conformal.chordBubble`, `OAI.CAT0Fillings.Conformal.chordBubbleD`, `OAI.CAT0Fillings.Conformal.chordBubbleDD`, `OAI.CAT0Fillings.Conformal.profile`, `OAI.CAT0Fillings.Conformal.profileGradient`, `OAI.CAT0Fillings.Conformal.profileRD`, `OAI.CAT0Fillings.Conformal.profileZD`, `OAI.CAT0Fillings.HasTwoPointMetricDifferential`, `OAI.CAT0Fillings.IntegerChart.coordinateEmptyChart`, `OAI.CAT0Fillings.IntegerChart.coordinateMinor`, `OAI.CAT0Fillings.IntegerChart.instMeasurableSpaceMatrixFinReal_1`, `OAI.CAT0Fillings.IntegerChart.negate`, `OAI.CAT0Fillings.IntegerChart.postcompose`, `OAI.CAT0Fillings.JointBV.DensityPiece`, `OAI.CAT0Fillings.JointBV.DirectionalVariation`, `OAI.CAT0Fillings.JointBV.LocalMeanBound`, `OAI.CAT0Fillings.JointBV.halfMean`, `OAI.CAT0Fillings.JointBV.indexTail`, `OAI.CAT0Fillings.JointBV.shrinkingBump`, `OAI.CAT0Fillings.MetricDifferentiation.HasCenteredMetricDifferential`, `OAI.CAT0Fillings.MetricDifferentiation.coordinateSeminorm`, `OAI.CAT0Fillings.MetricDifferentiation.lineSpeed` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CAT0Fillings_BV_JointPoincare`, `CAT0Fillings_BV_Oscillation`, `CAT0Fillings_BV_Poincare`, `CAT0Fillings_Bubble_Beta`, `CAT0Fillings_Bubble_Moments`, `CAT0Fillings_Calculus_AbsoluteValue`, `CAT0Fillings_Calculus_Bivariate`, `CAT0Fillings_Calculus_ClosedLevel`, `CAT0Fillings_Calculus_Piecewise`, `CAT0Fillings_Calculus_Polynomial`, `CAT0Fillings_Calculus_Smoothing`, `CAT0Fillings_Charts_CurrentAxioms`, `CAT0Fillings_Charts_ExtensionsLimit`, `CAT0Fillings_Charts_HilbertMass`, `CAT0Fillings_Charts_MeasurePartition`, `CAT0Fillings_Charts_Postcompose`, `CAT0Fillings_Charts_Straightening`, `CAT0Fillings_Chord_AverageProfile`, `CAT0Fillings_Chord_Barycenter`, `CAT0Fillings_Chord_Bubble`, `CAT0Fillings_Chord_Fubini`, `CAT0Fillings_Chord_TestIdentity`, `CAT0Fillings_Compactness_Borel`, `CAT0Fillings_Compactness_Tails`, `CAT0Fillings_Conformal_Closed`, `CAT0Fillings_Conformal_Growth`, `CAT0Fillings_Currents_CycleDifference`, `CAT0Fillings_Currents_Negation`, `CAT0Fillings_Currents_WeakMeasures`, `CAT0Fillings_Density_InverseCutoff`, `CAT0Fillings_Density_RadialEstimate`, `CAT0Fillings_Differentiation_Centered`, `CAT0Fillings_Differentiation_CurveSpeed`, `CAT0Fillings_Differentiation_Degenerate`, `CAT0Fillings_Differentiation_Density`, `CAT0Fillings_Differentiation_Directional`, `CAT0Fillings_Differentiation_ErrorModulus`, `CAT0Fillings_Differentiation_FullRank`, `CAT0Fillings_Differentiation_HilbertCharts`, `CAT0Fillings_Differentiation_LargePieces`, `CAT0Fillings_Differentiation_Seminorm`, `CAT0Fillings_Differentiation_TwoPoint`, `CAT0Fillings_Geometry_Ball`, `CAT0Fillings_Geometry_Comparison`, `CAT0Fillings_Geometry_Determinant`, `CAT0Fillings_Geometry_MatrixRows`, `CAT0Fillings_Gradient_Determinant`, `CAT0Fillings_Gradient_Multiplier`, `CAT0Fillings_Jacobian_ClosedForms`, `CAT0Fillings_Jacobian_Coordinates`, `CAT0Fillings_Jacobian_HeadEstimates`, `CAT0Fillings_Jacobian_Lipschitz`, `CAT0Fillings_Jacobian_Mixed`, `CAT0Fillings_Jacobian_Smoothing`, `CAT0Fillings_Jacobian_WeakLimits`, `CAT0Fillings_Powers_Truncated`, `CAT0Fillings_Prism_ClosedCylinder`, `CAT0Fillings_Radial_ClosedInequality`, `CAT0Fillings_Radial_IntegralDerivative`, `CAT0Fillings_Radial_MetricDerivative`, `CAT0Fillings_Radial_MetricSlope`, `CAT0Fillings_Radial_NormalizedDerivative`, `CAT0Fillings_Radial_SpatialForm`, `CAT0Fillings_Radial_TotalDeterminant`, `CAT0Fillings_Radial_TotalForm`, `CAT0Fillings_Radial_UniformSlope`, `CAT0Fillings_Rearrangement_Distribution`, `CAT0Fillings_Rearrangement_Euclidean`, `CAT0Fillings_Rearrangement_Inverse`, `CAT0Fillings_Reconstruction_AtomGraphs`, `CAT0Fillings_Reconstruction_BorelAtoms`, `CAT0Fillings_Reconstruction_GraphCharts`, `CAT0Fillings_Reconstruction_JointCharts`, `CAT0Fillings_Reconstruction_LipschitzPieces`, `CAT0Fillings_Reconstruction_ScalarCharts`, `CAT0Fillings_Scaling_Metric`, `CAT0Fillings_Slices_Approximation`, `CAT0Fillings_Slices_NormalBudget`, `CAT0Fillings_Slicing_CoordinateDerivative`, `CAT0Fillings_Slicing_CoordinateIntegral`, `CAT0Fillings_Sobolev_Truncation`, `CAT0Fillings_Swept_RadialChart`, `CAT0Fillings_Tangent_Blowup`, `CAT0Fillings_Tangent_CurrentDensity`, `CAT0Fillings_Tangent_Kernel`, `CAT0Fillings_Transport_RadialCDF`, `CAT0Fillings_Transport_Support`.
--
--   **Imports.** It imports the published bundle `Def_SharpCAT0Filling`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ29C0002`; the statements `OAI.CAT0Fillings.ChartGeometry.closed_added_tests` and `OAI.CAT0Fillings.Conformal.chordBubble_bounded_derivatives`; the proof of `OAI.CAT0Fillings.Conformal.chordBubble_bounded_derivatives`.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_SharpCAT0Filling

section
-- module Solutions.OAIQ29_C0.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ExtensionsLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace CAT0Fillings
variable {E : Type*} [PseudoMetricSpace E]
lemma lipschitzOn_limit {s : Set E} {K : ℝ≥0} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hs : ∀ j, LipschitzOnWith K (fs j) s)
    (hl : ∀ x ∈ s, Tendsto (fun j => fs j x) atTop (𝓝 (f x))) :
    LipschitzOnWith K f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact le_of_tendsto ((hl x hx).dist (hl y hy))
    (Eventually.of_forall fun j => (hs j).dist_le_mul x hx y hy)

lemma uniform_limit_on_totallyBounded {s : Set E} (hs : TotallyBounded s)
    {K : ℝ≥0} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hfs : ∀ j, LipschitzOnWith K (fs j) s)
    (hl : ∀ x ∈ s, Tendsto (fun j => fs j x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn fs f atTop s := by
  have hf := lipschitzOn_limit hfs hl
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (4 * ((K : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 4 * ((K : ℝ)+1) * δ = ε := by dsimp [δ]; field_simp
  obtain ⟨t, hts, ht, hcov⟩ := finite_approx_of_totallyBounded hs δ hδ
  have hpt : ∀ᶠ j in atTop, ∀ y ∈ t, dist (f y) (fs j y) < ε / 2 := by
    apply (ht.eventually_all.mpr)
    intro y hy
    have hh := (Metric.tendsto_atTop.mp (hl y (hts hy))) (ε/2) (half_pos hε)
    exact (eventually_atTop.mpr hh).mono fun j hj => by simpa only [dist_comm] using hj
  filter_upwards [hpt] with j hj x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hcov hx)
  have hd : dist x y < δ := hxy
  have H := dist_triangle4 (f x) (f y) (fs j y) (fs j x)
  have H₁ := hf.dist_le_mul x hx y (hts hyt)
  have H₂ := (hfs j).dist_le_mul y (hts hyt) x hx
  rw [dist_comm y x] at H₂
  have H₃ := hj y hyt
  have H₄ : (K : ℝ) * dist x y ≤ (K : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hd.le K.coe_nonneg
  nlinarith [K.coe_nonneg]

noncomputable def mcShane (s : Set E) (K : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  ⨅ z : s, f z + K * dist x z

lemma mcShane_bddBelow {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzOnWith K f s) (x : E) :
    BddBelow (range fun z : s => f z + K * dist x z) := by
  obtain ⟨z,hz⟩ := hs
  refine ⟨f z - K * dist x z, ?_⟩
  rintro w ⟨t,rfl⟩
  dsimp
  rw [_root_.sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist x t)]
  calc
    f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2
    _ ≤ f t + K * (dist x z + dist x t) := by gcongr; apply dist_triangle_left

lemma mcShane_eqOn {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzOnWith K f s) : EqOn f (mcShane s K f) s := by
  let : Nonempty s := hs.to_subtype
  intro x hx
  refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
  simpa only [mcShane, add_zero, Subtype.coe_mk, mul_zero, dist_self] using
    ciInf_le (mcShane_bddBelow hs hf x) ⟨x,hx⟩

lemma mcShane_lipschitz {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzOnWith K f s) : LipschitzWith K (mcShane s K f) := by
  let : Nonempty s := hs.to_subtype
  apply LipschitzWith.of_le_add_mul
  intro x y
  rw [← _root_.sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [_root_.sub_le_iff_le_add]
  calc
    mcShane s K f x ≤ f z + K * dist x z := ciInf_le (mcShane_bddBelow hs hf x) _
    _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      apply dist_triangle

lemma mcShane_dist_le {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f g : E → ℝ}
    (hf : LipschitzOnWith K f s) (hg : LipschitzOnWith K g s)
    {ε : ℝ} (hε : ∀ x ∈ s, dist (f x) (g x) ≤ ε) (x : E) :
    dist (mcShane s K f x) (mcShane s K g x) ≤ ε := by
  let : Nonempty s := hs.to_subtype
  have aux {f g : E → ℝ} (hf : LipschitzOnWith K f s)
      (h : ∀ z ∈ s, f z ≤ g z + ε) :
      mcShane s K f x - ε ≤ mcShane s K g x := by
    apply le_ciInf
    intro z
    have H := ciInf_le (mcShane_bddBelow hs hf x) z
    change mcShane s K f x ≤ f z + K * dist x z at H
    linarith [h z z.2]
  rw [Real.dist_eq, abs_le]
  have H₁ := aux (g := g) hf (fun z hz => by have H := (abs_le.mp (hε z hz)).2; linarith)
  have H₂ := aux (g := f) hg (fun z hz => by have H := (abs_le.mp (hε z hz)).1; linarith)
  constructor <;> linarith

lemma exists_convergent_lipschitz_extensions {s : Set E} (hs : TotallyBounded s)
    {K : ℝ≥0} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hfs : ∀ j, LipschitzOnWith K (fs j) s)
    (hl : ∀ x ∈ s, Tendsto (fun j => fs j x) atTop (𝓝 (f x))) :
    ∃ (Fs : ℕ → E → ℝ) (F : E → ℝ),
      (∀ j, LipschitzWith K (Fs j)) ∧ LipschitzWith K F ∧
      (∀ j, EqOn (fs j) (Fs j) s) ∧ EqOn f F s ∧
      ∀ x, Tendsto (fun j => Fs j x) atTop (𝓝 (F x)) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ _ => 0,fun _ => 0,fun _ => (LipschitzWith.const _).weaken (by positivity),
      (LipschitzWith.const _).weaken (by positivity),fun _ => eqOn_empty _ _,
      eqOn_empty _ _,fun _ => tendsto_const_nhds⟩
  have hf := lipschitzOn_limit hfs hl
  refine ⟨fun j => mcShane s K (fs j),mcShane s K f,
    fun j => mcShane_lipschitz hsne (hfs j),mcShane_lipschitz hsne hf,
    fun j => mcShane_eqOn hsne (hfs j),mcShane_eqOn hsne hf,?_⟩
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have HU := Metric.tendstoUniformlyOn_iff.mp (uniform_limit_on_totallyBounded hs hfs hl)
    (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp HU
  refine ⟨N,fun j hj => ?_⟩
  have HH := mcShane_dist_le hsne hf (hfs j) (fun z hz => (hN j hj z hz).le) x
  rw [dist_comm] at HH
  exact HH.trans_lt (half_lt_self hε)

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_ClosedForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma integral_fderiv_compact_eq_zero {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (v : E) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hI : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hfc
  have hD : Integrable (fun x => fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ v)
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : E => (1 : ℝ)) (g := f) (v := v) (μ := μ)
    (by simp) (by simpa using hD) (by simpa using hI)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => hf.differentiable (by norm_num) x)
  simpa using H

lemma integral_extDeriv_scalar_eq_zero {n : ℕ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} (hω : Differentiable ℝ ω)
    (hωc : HasCompactSupport ω)
    (hs : ∀ w : Fin n → E, ContDiff ℝ 1 (fun x => ω x w))
    (v : Fin (n+1) → E) : (∫ x, extDeriv ω x v ∂μ) = 0 := by
  have hc (i : Fin (n+1)) : HasCompactSupport (fun x => ω x (i.removeNth v)) :=
    hωc.comp_left (g := fun a : E [⋀^Fin n]→L[ℝ] ℝ => a (i.removeNth v)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hI (i : Fin (n+1)) : Integrable
      (fun x => (-1 : ℝ)^i.val * fderiv ℝ (fun y => ω y (i.removeNth v)) x (v i)) μ := by
    apply Integrable.const_mul
    exact (((hs _).continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hc i).fderiv_apply ℝ (v i))
  simp_rw [extDeriv_apply (hω _)]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp only [integral_const_mul, integral_fderiv_compact_eq_zero μ (hs _) (hc _), mul_zero,
    Finset.sum_const_zero]

noncomputable def rowVolume (n : ℕ) : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

lemma rowVolume_apply {n : ℕ} (w : Fin n → (Fin n → ℝ)) :
    rowVolume n w = Matrix.det w := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma extDeriv_mul_form {n : ℕ} {f : E → ℝ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hω : DifferentiableAt ℝ ω x)
    (v : Fin (n+1) → E) :
    extDeriv (fun z => f z • ω z) x v =
      f x * extDeriv ω x v +
        ∑ i, (-1 : ℝ)^i.val * fderiv ℝ f x (v i) * ω x (i.removeNth v) := by
  rw [extDeriv, fderiv_fun_smul hf hω,
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma closed_pullback_rowVolume {n : ℕ} {g : E → Fin n → ℝ}
    (hg : ContDiff ℝ 2 g) (x : E) :
    extDeriv (fun z => (rowVolume n).compContinuousLinearMap (fderiv ℝ g z)) x = 0 := by
  have H := extDeriv_pullback (ω := fun _ : Fin n → ℝ => rowVolume n)
    (f := g) (x := x) (differentiableAt_const _) hg.contDiffAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  rw [H]
  ext v
  simp [extDeriv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]

lemma integral_smooth_jacobian_eq_zero {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (v : Fin (n+1) → E) :
    (∫ x, Matrix.det (Matrix.of (fun i =>
      Matrix.vecCons (fderiv ℝ f x (v i)) (fderiv ℝ g x (v i)))) ∂μ) = 0 := by
  let α : E → E [⋀^Fin n]→L[ℝ] ℝ :=
    fun x => (rowVolume n).compContinuousLinearMap (fderiv ℝ g x)
  have hg' : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hα (x : E) : DifferentiableAt ℝ α x :=
    (differentiableAt_const _).continuousAlternatingMapCompContinuousLinearMap
      (hg'.differentiable one_ne_zero x)
  have hs (w : Fin n → E) : ContDiff ℝ 1 (fun x => α x w) := by
    exact (rowVolume n).toContinuousMultilinearMap.contDiff.comp
      (contDiff_pi.mpr (fun i => hg'.clm_apply contDiff_const))
  have hω : Differentiable ℝ (fun x => f x • α x) :=
    fun x => (hf.differentiable one_ne_zero x).smul (hα x)
  have H := integral_extDeriv_scalar_eq_zero μ hω hfc.smul_right
    (fun w => by simpa using hf.mul (hs w)) v
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards with x
  rw [extDeriv_mul_form (hf.differentiable one_ne_zero x) (hα x)]
  change _ = f x * extDeriv (fun z => (rowVolume n).compContinuousLinearMap
    (fderiv ℝ g z)) x v + _
  rw [closed_pullback_rowVolume hg x]
  simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero, zero_add]
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.of_apply, Matrix.cons_val_zero, α,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, rowVolume_apply]
  congr 2

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_Mixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
noncomputable def mixedJacobian {n : ℕ} (f : E → ℝ) (g : E → Fin n → ℝ)
    (v : Fin (n+1) → E) (x : E) : ℝ :=
  Matrix.det (Matrix.of (fun i => Matrix.vecCons (fderiv ℝ f x (v i))
    (fderiv ℝ g x (v i))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : Fin (n+1) → E) :
    Continuous (mixedJacobian f g v) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact (continuous_apply j).comp
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixedJacobian_eq_zero_of_fderiv_eq_zero {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (v : Fin (n+1) → E) {x : E} (h : fderiv ℝ f x = 0) :
    mixedJacobian f g v x = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (0 : Fin (n+1))
  intro i
  simp [h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasCompactSupport_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : HasCompactSupport f) (v : Fin (n+1) → E) :
    HasCompactSupport (mixedJacobian f g v) := by
  apply (hf.fderiv ℝ).mono
  intro x hx
  contrapose! hx
  simpa using (mixedJacobian_eq_zero_of_fderiv_eq_zero (g := g) v (by simpa using hx))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixedJacobian_mul {n : ℕ} {f h : E → ℝ} {g : E → Fin n → ℝ}
    {x : E} (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x)
    (v : Fin (n+1) → E) :
    mixedJacobian (fun y => f y * h y) g v x =
      f x * mixedJacobian h g v x + h x * mixedJacobian f g v x := by
  have hprod (i : Fin (n+1)) : fderiv ℝ (fun y => f y * h y) x (v i) =
      f x * fderiv ℝ h x (v i) + h x * fderiv ℝ f x (v i) := by
    rw [fderiv_fun_mul hf hh]
    rfl
  simp only [mixedJacobian, Matrix.det_succ_column_zero, Matrix.of_apply,
    Matrix.cons_val_zero, hprod]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.submatrix, Matrix.of_apply, Matrix.cons_val_succ]
  ring

lemma integral_smooth_mixedJacobian_mul {n : ℕ} {f h : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hh : ContDiff ℝ 1 h)
    (hg : ContDiff ℝ 2 g) (v : Fin (n+1) → E) :
    (∫ x, f x * mixedJacobian h g v x ∂μ) =
      -(∫ x, h x * mixedJacobian f g v x ∂μ) := by
  have hgc : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hI₁ : Integrable (fun x => f x * mixedJacobian h g v x) μ :=
    (hf.continuous.mul (continuous_mixedJacobian hh hgc v)).integrable_of_hasCompactSupport
      hfc.mul_right
  have hI₂ : Integrable (fun x => h x * mixedJacobian f g v x) μ :=
    (hh.continuous.mul (continuous_mixedJacobian hf hgc v)).integrable_of_hasCompactSupport
      (hasCompactSupport_mixedJacobian hfc v).mul_left
  have H := integral_smooth_jacobian_eq_zero μ (hf.mul hh) hfc.mul_right hg v
  change (∫ x, mixedJacobian (fun y => f y * h y) g v x ∂μ) = 0 at H
  simp_rw [mixedJacobian_mul (hf.differentiable one_ne_zero _) (hh.differentiable one_ne_zero _)] at H
  rw [integral_add hI₁ hI₂] at H
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_mixedJacobian_bound {n : ℕ} (K L : ℝ) (v : Fin (n+1) → E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : E → ℝ) (g : E → Fin n → ℝ) x,
      ‖fderiv ℝ f x‖ ≤ K → ‖fderiv ℝ g x‖ ≤ L →
      ‖mixedJacobian f g v x‖ ≤ B := by
  let D := (E →L[ℝ] ℝ) × (E →L[ℝ] (Fin n → ℝ))
  let J : D → ℝ := fun p => Matrix.det (Matrix.of fun i => Matrix.vecCons (p.1 (v i)) (p.2 (v i)))
  have hc : Continuous J := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    exact (continuous_fst.clm_apply continuous_const).matrixVecCons
      (continuous_snd.clm_apply continuous_const)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : E →L[ℝ] ℝ) K).prod
    (isCompact_closedBall (0 : E →L[ℝ] (Fin n → ℝ)) L)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|, abs_nonneg _, fun f g x hf hg => ?_⟩
  apply (hB (fderiv ℝ f x, fderiv ℝ g x) ?_).trans (le_abs_self B)
  exact ⟨by simpa using hf, by simpa using hg⟩

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
lemma aestronglyMeasurable_mixedJacobian {n : ℕ} (f : E → ℝ) (g : E → Fin n → ℝ)
    (v : Fin (n+1) → E) : AEStronglyMeasurable (mixedJacobian f g v) μ := by
  have h : Measurable (mixedJacobian f g v) := by
    unfold mixedJacobian
    simp only [Matrix.det_apply']
    fun_prop
  exact h.aestronglyMeasurable

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] [BorelSpace E] in
lemma ae_tendsto_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    {fs : ℕ → E → ℝ} {gs : ℕ → E → Fin n → ℝ}
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (fs j) x) atTop (𝓝 (fderiv ℝ f x)))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (gs j) x) atTop (𝓝 (fderiv ℝ g x)))
    (v : Fin (n+1) → E) :
    ∀ᵐ x ∂μ, Tendsto (fun j => mixedJacobian (fs j) (gs j) v x) atTop
      (𝓝 (mixedJacobian f g v x)) := by
  filter_upwards [hf, hg] with x hx hy
  have H : Continuous (fun p : (E →L[ℝ] ℝ) × (E →L[ℝ] (Fin n → ℝ)) =>
      Matrix.det (Matrix.of fun i => Matrix.vecCons (p.1 (v i)) (p.2 (v i)))) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    exact (continuous_fst.clm_apply continuous_const).matrixVecCons
      (continuous_snd.clm_apply continuous_const)
  exact H.continuousAt.tendsto.comp (hx.prodMk_nhds hy)

omit [IsAddHaarMeasure μ] in
lemma tendsto_integral_weighted_mixedJacobian {n : ℕ} {f : E → ℝ} {g : E → Fin n → ℝ}
    {fs : ℕ → E → ℝ} {gs : ℕ → E → Fin n → ℝ} {as : ℕ → E → ℝ} {a A : E → ℝ}
    {K L : ℝ} (hK : ∀ j x, ‖fderiv ℝ (fs j) x‖ ≤ K)
    (hL : ∀ j x, ‖fderiv ℝ (gs j) x‖ ≤ L)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (fs j) x) atTop (𝓝 (fderiv ℝ f x)))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (gs j) x) atTop (𝓝 (fderiv ℝ g x)))
    (ha : ∀ j, AEStronglyMeasurable (as j) μ)
    (hac : ∀ᵐ x ∂μ, Tendsto (fun j => as j x) atTop (𝓝 (a x)))
    (hA : Integrable A μ) (haA : ∀ j, ∀ᵐ x ∂μ, ‖as j x‖ ≤ A x)
    (v : Fin (n+1) → E) :
    Tendsto (fun j => ∫ x, as j x * mixedJacobian (fs j) (gs j) v x ∂μ) atTop
      (𝓝 (∫ x, a x * mixedJacobian f g v x ∂μ)) := by
  obtain ⟨B, _, hB⟩ := exists_mixedJacobian_bound K L v
  apply tendsto_integral_of_dominated_convergence (fun x => A x * B)
  · exact fun j => (ha j).mul (aestronglyMeasurable_mixedJacobian μ _ _ _)
  · exact hA.mul_const B
  · intro j
    filter_upwards [haA j] with x hx
    rw [norm_mul]
    exact mul_le_mul hx (hB _ _ _ (hK j x) (hL j x)) (norm_nonneg _) ((norm_nonneg _).trans hx)
  · filter_upwards [hac, ae_tendsto_mixedJacobian μ hf hg v] with x hx hy
    exact hx.mul hy

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma uniformly_bounded_lipschitz_on_compact {fs : ℕ → E → ℝ} {f : E → ℝ}
    {K : ℝ≥0} (hK : ∀ j, LipschitzWith K (fs j))
    (hf : Tendsto (fun j => fs j 0) atTop (𝓝 (f 0))) {s : Set E} (hs : IsCompact s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ s → ‖fs j x‖ ≤ B := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hf).exists_norm_le
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le
  refine ⟨K * |R| + |C|, by positivity, fun j x hx => ?_⟩
  calc ‖fs j x‖ ≤ ‖fs j x - fs j 0‖ + ‖fs j 0‖ := norm_le_norm_sub_add _ _
    _ ≤ K * ‖x‖ + C := by
      gcongr
      · simpa [dist_eq_norm] using (hK j).dist_le_mul x 0
      · exact hC _ (mem_range_self j)
    _ ≤ K * |R| + |C| := by gcongr; exact (hR x hx).trans (le_abs_self R); exact le_abs_self C

end CAT0Fillings

open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings.VectorSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma hasFDerivAt_convolution_lipschitz {f : E → F} {g : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) (hgc : HasCompactSupport g) (x : E) :
    HasFDerivAt (g ⋆[lsmul ℝ ℝ, μ] f)
      ((g ⋆[lsmul ℝ ℝ, μ] (fderiv ℝ f)) x) x := by
  have hsub := (μ.measurePreserving_sub_left x).quasiMeasurePreserving
  have hD : ∀ᵐ t ∂μ, DifferentiableAt ℝ f (x - t) :=
    hsub.ae (hf.ae_differentiableAt (μ := μ))
  have hgI := hg.integrable_of_hasCompactSupport (μ := μ) hgc
  have hFI (y : E) : Integrable (fun t => g t • f (y-t)) μ :=
    (hg.smul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hgc.smul_right
  have hDm : AEStronglyMeasurable (fun t => g t • fderiv ℝ f (x-t)) μ :=
    hg.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hdif : ∀ᵐ t ∂μ, HasFDerivAt (fun y => g t • f (y-t))
      (g t • fderiv ℝ f (x-t)) x := by
    filter_upwards [hD] with t ht
    have H := ((ht.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const t)).const_smul (g t))
    change HasFDerivAt (fun y => g t • f (y-t)) _ x at H
    simpa using H
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ (univ : Set E),
      ‖g t • f (y-t) - g t • f (x-t)‖ ≤ (‖g t‖ * K) * ‖y-x‖ := by
    filter_upwards with t y _
    rw [← smul_sub, norm_smul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa [dist_eq_norm] using hf.dist_le_mul (y-t) (x-t)
  have H := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := μ) (s := univ) (F := fun y t => g t • f (y-t))
    (F' := fun t => g t • fderiv ℝ f (x-t)) (bound := fun t => ‖g t‖ * K)
    (x₀ := x) univ_mem (fun y _ => (hFI y).aestronglyMeasurable) (hFI x)
    hDm hbound (hgI.norm.mul_const K) hdif
  simpa +unfoldPartialApp [convolution, lsmul_apply] using H.2

lemma locallyIntegrable_fderiv_lipschitz {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LocallyIntegrable (fderiv ℝ f) μ := by
  apply (locallyIntegrable_const (μ := μ) (K : ℝ)).mono
    (measurable_fderiv ℝ f).aestronglyMeasurable
  filter_upwards with x
  simpa using norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)

lemma fderiv_bump_convolution {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x =
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x) :=
  (hasFDerivAt_convolution_lipschitz μ hf (φ.contDiff_normed (n := 1)).continuous
    φ.hasCompactSupport_normed x).fderiv

lemma ae_fderiv_bump_convolution_tendsto {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} {C : ℝ}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ' : ∀ᶠ i in l, (φ i).rOut ≤ C * (φ i).rIn) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  simp_rw [fderiv_bump_convolution μ hf]
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφ'
    (locallyIntegrable_fderiv_lipschitz μ hf)

lemma norm_fderiv_bump_convolution_le {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ K := by
  rw [fderiv_bump_convolution μ hf, convolution_def]
  have hI := ((φ.contDiff_normed (μ := μ) (n := 1)).continuous.integrable_of_hasCompactSupport
    (μ := μ) φ.hasCompactSupport_normed).mul_const (K : ℝ)
  have H := norm_integral_le_of_norm_le hI (Eventually.of_forall (fun t => show
      ‖lsmul ℝ ℝ (φ.normed μ t) (fderiv ℝ f (x-t))‖ ≤ φ.normed μ t * K from by
    rw [lsmul_apply, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf) (φ.nonneg_normed t)))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using H

lemma lipschitzWith_bump_convolution {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) :
    LipschitzWith K (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun x => (hasFDerivAt_convolution_lipschitz μ hf
      (φ.contDiff_normed (n := 1)).continuous φ.hasCompactSupport_normed x).differentiableAt
  · intro x
    exact_mod_cast norm_fderiv_bump_convolution_le μ hf φ x

lemma contDiff_bump_convolution {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (n : ℕ∞) :
    ContDiff ℝ n (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.continuous.locallyIntegrable

noncomputable def shrinkingBump (j : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (j + 1 : ℝ)
  rOut := 2 / (j + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma shrinkingBump_tendsto : Tendsto (fun j : ℕ => (shrinkingBump (E := E) j).rOut)
    atTop (𝓝 0) := by
  simpa [shrinkingBump, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))

lemma exists_smooth_lipschitz_approximation {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ∃ f' : ℕ → E → F,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f' j) ∧ LipschitzWith K (f' j)) ∧
      (∀ x, Tendsto (fun j => f' j x) atTop (𝓝 (f x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (f' j) x) atTop (𝓝 (fderiv ℝ f x))) := by
  refine ⟨fun j => (shrinkingBump j).normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, ?_, ?_⟩
  · intro j
    exact ⟨contDiff_bump_convolution μ hf _ ⊤, lipschitzWith_bump_convolution μ hf _⟩
  · exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hf.continuous
  · apply ae_fderiv_bump_convolution_tendsto μ hf shrinkingBump_tendsto (C := 2)
    filter_upwards with j
    dsimp [shrinkingBump]
    ring_nf
    rfl

end CAT0Fillings.VectorSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_Lipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma integral_lipschitz_mixedJacobian_mul {n : ℕ} {f h : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {K L : ℝ≥0}
    (hh : LipschitzWith K h) (hg : LipschitzWith L g) (v : Fin (n+1) → E) :
    (∫ x, f x * mixedJacobian h g v x ∂μ) =
      -(∫ x, h x * mixedJacobian f g v x ∂μ) := by
  obtain ⟨hs, hhs, hhlim, hhD⟩ := VectorSmoothing.exists_smooth_lipschitz_approximation μ hh
  obtain ⟨gs, hgs, hglim, hgD⟩ := VectorSmoothing.exists_smooth_lipschitz_approximation μ hg
  have hfI : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hfc
  have H₁ := tendsto_integral_weighted_mixedJacobian μ
    (fs := hs) (gs := gs) (as := fun _ => f) (a := f) (A := fun x => ‖f x‖)
    (K := K) (L := L)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ (hhs j).2)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ (hgs j).2)
    hhD hgD (fun _ => hfI.aestronglyMeasurable) (Eventually.of_forall (fun _ => tendsto_const_nhds))
    hfI.norm (fun _ => Eventually.of_forall fun _ => le_rfl) v
  obtain ⟨N, hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf one_ne_zero
  obtain ⟨B, hB0, hB⟩ := uniformly_bounded_lipschitz_on_compact
    (fun j => (hhs j).2) (hhlim 0) hfc
  have hAd : Integrable ((tsupport f).indicator (fun _ : E => B)) μ := by
    apply (integrable_indicator_iff (isClosed_tsupport f).measurableSet).2
    exact continuous_const.continuousOn.integrableOn_compact hfc
  have Hd : ∀ j, AEStronglyMeasurable ((tsupport f).indicator (hs j)) μ :=
    fun j => (hhs j).2.continuous.aestronglyMeasurable.indicator (isClosed_tsupport f).measurableSet
  have Hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (tsupport f).indicator (hs j) x) atTop
      (𝓝 ((tsupport f).indicator h x)) := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · simpa [hx] using hhlim x
    · simp [hx]
  have Hbound : ∀ j, ∀ᵐ x ∂μ,
      ‖(tsupport f).indicator (hs j) x‖ ≤ (tsupport f).indicator (fun _ => B) x := by
    intro j
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · simpa [hx] using hB j x hx
    · simp [hx]
  have H₂ := tendsto_integral_weighted_mixedJacobian μ
    (fs := fun _ => f) (gs := gs) (as := fun j => (tsupport f).indicator (hs j))
    (a := (tsupport f).indicator h) (K := N) (L := L)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ hN)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ (hgs j).2)
    (Eventually.of_forall (fun _ => tendsto_const_nhds)) hgD Hd Hlim hAd Hbound v
  have hcut (u : E → ℝ) (g' : E → Fin n → ℝ) :
      (fun x => (tsupport f).indicator u x * mixedJacobian f g' v x) =
        (fun x => u x * mixedJacobian f g' v x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · simp [hx]
    · rw [mixedJacobian_eq_zero_of_fderiv_eq_zero v (fderiv_of_notMem_tsupport ℝ hx)]
      simp
  simp_rw [hcut] at H₂
  have heq : (fun j => ∫ x, f x * mixedJacobian (hs j) (gs j) v x ∂μ) =
      fun j => -(∫ x, hs j x * mixedJacobian f (gs j) v x ∂μ) := by
    funext j
    exact integral_smooth_mixedJacobian_mul μ hf hfc ((hhs j).1.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
      ((hgs j).1.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) v
  rw [heq] at H₁
  exact tendsto_nhds_unique H₁ H₂.neg

end CAT0Fillings

open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma continuous_compact_smooth_L1_approx {p : E → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      (∫ x, ‖p x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨R, hR⟩ := hpc.isBounded.exists_norm_le
  let φ : ContDiffBump (0 : E) := ⟨|R|+1, |R|+2, by positivity, by linarith⟩
  have hpφ (x : E) : φ x * p x = p x := by
    by_cases hx : p x = 0
    · simp [hx]
    · have H : φ x = 1 := φ.one_of_mem_closedBall (by
        simpa [φ] using (hR x (subset_tsupport p hx)).trans
          ((le_abs_self R).trans (by linarith : |R| ≤ |R|+1)))
      simp [H]
  let S := tsupport (φ : E → ℝ)
  have hSc : IsCompact S := φ.hasCompactSupport
  have hSm : MeasurableSet S := hSc.measurableSet
  let δ := ε / (μ.real S + 1)
  have hμ : 0 ≤ μ.real S := measureReal_nonneg
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨q, hq, hpq⟩ := (hpc.uniformContinuous_of_continuous hp).exists_contDiff_dist_le hδ
  refine ⟨fun x => φ x * q x, φ.contDiff.mul (hq.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)), φ.hasCompactSupport.mul_right, ?_⟩
  have hPI : Integrable p μ := hp.integrable_of_hasCompactSupport hpc
  have hQI : Integrable (fun x => φ x * q x) μ :=
    (φ.continuous.mul hq.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hAI : Integrable (S.indicator (fun _ : E => δ)) μ :=
    (integrable_indicator_iff hSm).2 (continuous_const.continuousOn.integrableOn_compact hSc)
  have hbd : ∀ x, ‖p x - φ x * q x‖ ≤ S.indicator (fun _ => δ) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      calc ‖p x - φ x * q x‖ = ‖φ x * (p x-q x)‖ := by rw [mul_sub, hpφ]
        _ ≤ ‖p x-q x‖ := by
          rw [norm_mul, Real.norm_of_nonneg φ.nonneg]
          exact mul_le_of_le_one_left (norm_nonneg _) φ.le_one
        _ ≤ δ := by simpa [dist_eq_norm, norm_sub_rev] using (hpq x).le
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hpx : p x = 0 := by simpa [hφx] using (hpφ x).symm
      simp [hx, hφx, hpx]
  calc (∫ x, ‖p x - φ x * q x‖ ∂μ) ≤ ∫ x, S.indicator (fun _ : E => δ) x ∂μ :=
      integral_mono_ae (hPI.sub hQI).norm hAI (Eventually.of_forall hbd)
    _ = μ.real S * δ := by rw [integral_indicator hSm]; simp [measureReal_def]
    _ ≤ ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < μ.real S + 1)]
      nlinarith

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma integrable_smooth_compact_L1_approx {f : E → ℝ} (hf : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨p, hpc, hfp, hp, hpI⟩ := hf.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  obtain ⟨g, hg, hgc, hpg⟩ := continuous_compact_smooth_L1_approx μ hp hpc (half_pos hε)
  refine ⟨g, hg, hgc, ?_⟩
  have hgI := hg.continuous.integrable_of_hasCompactSupport (μ := μ) hgc
  have htriangle : (∫ x, ‖f x-g x‖ ∂μ) ≤
      (∫ x, (‖f x-p x‖ + ‖p x-g x‖) ∂μ) := by
    refine integral_mono_ae (hf.sub hgI).norm ((hf.sub hpI).norm.add (hpI.sub hgI).norm) ?_
    filter_upwards with x
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hadd := integral_add (hf.sub hpI).norm (hpI.sub hgI).norm
  simp only [Pi.sub_apply] at hadd
  rw [hadd] at htriangle
  linarith

end CAT0Fillings

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

noncomputable def coordinateJacobian {n : ℕ} (f : Fin n → E → ℝ)
    (v : Fin n → E) (x : E) : ℝ := Matrix.det (Matrix.of fun i j => fderiv ℝ (f j) x (v i))

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
lemma measurable_coordinateJacobian {n : ℕ} (f : Fin n → E → ℝ) (v : Fin n → E) :
    Measurable (coordinateJacobian f v) := by
  unfold coordinateJacobian
  simp only [Matrix.det_apply']
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
lemma coordinateJacobian_uniform_bound {n : ℕ} (K : ℝ≥0) (v : Fin n → E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : Fin n → E → ℝ, (∀ i, LipschitzWith K (f i)) →
      ∀ x, ‖coordinateJacobian f v x‖ ≤ B := by
  let J : (Fin n → E →L[ℝ] ℝ) → ℝ := fun p => Matrix.det (Matrix.of fun i j => p j (v i))
  have hc : Continuous J := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j).clm_apply continuous_const
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin n → E →L[ℝ] ℝ) K).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|, abs_nonneg _, fun f hf x => ?_⟩
  apply (hB (fun i => fderiv ℝ (f i) x) ?_).trans (le_abs_self B)
  simpa only [mem_closedBall, dist_zero_right] using
    (pi_norm_le_iff_of_nonneg K.coe_nonneg).2 (fun i => norm_fderiv_le_of_lipschitz ℝ (hf i))

omit [IsAddHaarMeasure μ] in
lemma integrable_mul_coordinateJacobian {n : ℕ} {a : E → ℝ} (ha : Integrable a μ)
    {f : Fin n → E → ℝ} {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (v : Fin n → E) : Integrable (fun x => a x * coordinateJacobian f v x) μ := by
  obtain ⟨B, _, hB⟩ := coordinateJacobian_uniform_bound K v
  refine (ha.norm.mul_const B).mono'
    (ha.aestronglyMeasurable.mul (measurable_coordinateJacobian f v).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB f hf x) (norm_nonneg _)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lipschitz_coordinate_tuple {n : ℕ} {f : Fin n → E → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) : LipschitzWith K (fun x i => f i x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).2
  intro i
  exact (hf i).dist_le_mul x y

lemma ae_coordinateJacobian_cons {n : ℕ} {h : E → ℝ} {g : Fin n → E → ℝ}
    {K : ℝ≥0} (hg : ∀ i, LipschitzWith K (g i)) (v : Fin (n+1) → E) :
    coordinateJacobian (Fin.cons h g) v =ᵐ[μ]
      mixedJacobian h (fun x i => g i x) v := by
  have hd := (ae_all_iff.mpr (fun i => (hg i).ae_differentiableAt (μ := μ)))
  filter_upwards [hd] with x hx
  unfold coordinateJacobian mixedJacobian
  rw [fderiv_pi hx]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coordinateJacobian_cons {n : ℕ} (h : E → ℝ) (g : Fin n → E → ℝ)
    (v : Fin (n+1) → E) (x : E) :
    coordinateJacobian (Fin.cons h g) v x =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val * fderiv ℝ h x (v i) *
        coordinateJacobian g (i.removeNth v) x := by
  unfold coordinateJacobian
  rw [Matrix.det_succ_column_zero]
  rfl

lemma integral_coordinateJacobian_cons {n : ℕ} {f h : E → ℝ}
    {g : Fin n → E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {K L : ℝ≥0} (hh : LipschitzWith K h) (hg : ∀ i, LipschitzWith L (g i))
    (v : Fin (n+1) → E) :
    (∫ x, f x * coordinateJacobian (Fin.cons h g) v x ∂μ) =
      -(∫ x, h x * coordinateJacobian (Fin.cons f g) v x ∂μ) := by
  have H := integral_lipschitz_mixedJacobian_mul μ hf hfc hh (lipschitz_coordinate_tuple hg) v
  calc (∫ x, f x * coordinateJacobian (Fin.cons h g) v x ∂μ) =
      (∫ x, f x * mixedJacobian h (fun x i => g i x) v x ∂μ) := by
        apply integral_congr_ae
        filter_upwards [ae_coordinateJacobian_cons μ (h := h) hg v] with x hx
        rw [hx]
    _ = -(∫ x, h x * mixedJacobian f (fun x i => g i x) v x ∂μ) := H
    _ = -(∫ x, h x * coordinateJacobian (Fin.cons f g) v x ∂μ) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_coordinateJacobian_cons μ (h := f) hg v] with x hx
        rw [hx]

end CAT0Fillings

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [IsAddHaarMeasure μ] in
lemma tendsto_integral_mul_uniformly_bounded {as Js : ℕ → E → ℝ}
    {A : E → ℝ} {B : ℝ}
    (hA : Integrable A μ) (ha : ∀ j, AEStronglyMeasurable (as j) μ)
    (hJ : ∀ j, AEStronglyMeasurable (Js j) μ)
    (haA : ∀ j, ∀ᵐ x ∂μ, ‖as j x‖ ≤ A x)
    (hJB : ∀ j x, ‖Js j x‖ ≤ B)
    (halim : ∀ᵐ x ∂μ, Tendsto (fun j => as j x) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, as j x * Js j x ∂μ) atTop (𝓝 0) := by
  have H := tendsto_integral_of_dominated_convergence (fun x => A x * B)
    (fun j => (ha j).mul (hJ j)) (hA.mul_const B)
    (fun j => by
      filter_upwards [haA j] with x hx
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul hx (hJB j x) (norm_nonneg _) ((norm_nonneg _).trans hx))
    (show ∀ᵐ x ∂μ, Tendsto (fun j => as j x * Js j x) atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [halim] with x hx
      refine squeeze_zero_norm (a := fun j => ‖as j x‖ * B) ?_ ?_
      · intro j
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hJB j x) (norm_nonneg _)
      · simpa using hx.norm.mul_const B)
  simpa using H

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_HeadEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
omit [FiniteDimensional ℝ E] in
lemma integrable_continuous_mul_compact_fderiv {u η : E → ℝ}
    (hu : Continuous u) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (v : E) (c : ℝ) :
    Integrable (fun x => u x * c * fderiv ℝ η x v) μ := by
  exact ((hu.mul continuous_const).mul
    ((hη.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hηc.fderiv_apply ℝ v).mul_left

lemma integral_coordinateJacobian_expand {n : ℕ} {u η : E → ℝ}
    {g : Fin n → E → ℝ} (hu : Continuous u) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) {K : ℝ≥0} (hg : ∀ i, LipschitzWith K (g i))
    (v : Fin (n+1) → E) :
    (∫ x, u x * coordinateJacobian (Fin.cons η g) v x ∂μ) =
      ∑ i : Fin (n+1), ∫ x, (u x * (-1 : ℝ)^i.val * fderiv ℝ η x (v i)) *
        coordinateJacobian g (i.removeNth v) x ∂μ := by
  simp_rw [coordinateJacobian_cons, Finset.mul_sum]
  have heq (x : E) (i : Fin (n+1)) :
      u x * ((-1 : ℝ)^i.val * fderiv ℝ η x (v i) * coordinateJacobian g (i.removeNth v) x) =
        (u x * (-1 : ℝ)^i.val * fderiv ℝ η x (v i)) * coordinateJacobian g (i.removeNth v) x := by ring
  simp_rw [heq]
  exact integral_finsetSum _ (fun i _ => integrable_mul_coordinateJacobian μ
    (integrable_continuous_mul_compact_fderiv μ hu hη hηc (v i) _) hg (i.removeNth v))

omit [IsAddHaarMeasure μ] in
lemma integral_weight_coordinateJacobian_difference_bound {n : ℕ} {a b : E → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) {f : Fin n → E → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (v : Fin n → E) {B : ℝ}
    (hB : ∀ x, ‖coordinateJacobian f v x‖ ≤ B) :
    ‖(∫ x, a x * coordinateJacobian f v x ∂μ) -
      (∫ x, b x * coordinateJacobian f v x ∂μ)‖ ≤
        (∫ x, ‖a x-b x‖ ∂μ) * B := by
  rw [← integral_sub (integrable_mul_coordinateJacobian μ ha hf v)
    (integrable_mul_coordinateJacobian μ hb hf v)]
  simp_rw [← sub_mul]
  calc ‖∫ x, (a x - b x) * coordinateJacobian f v x ∂μ‖ ≤
      ∫ x, ‖a x-b x‖ * B ∂μ := by
        refine norm_integral_le_of_norm_le ((ha.sub hb).norm.mul_const B) ?_
        filter_upwards with x
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = _ := integral_mul_const B _

end CAT0Fillings

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma integrable_coordinateJacobian_cons_weight {n : ℕ} {u η : E → ℝ}
    {g : Fin n → E → ℝ} (hu : Continuous u) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) {K : ℝ≥0} (hg : ∀ i, LipschitzWith K (g i))
    (v : Fin (n+1) → E) :
    Integrable (fun x => u x * coordinateJacobian (Fin.cons η g) v x) μ := by
  have H := integrable_finsetSum (s := Finset.univ) (fun i _ =>
    integrable_mul_coordinateJacobian μ
      (integrable_continuous_mul_compact_fderiv μ hu hη hηc (v i) ((-1 : ℝ)^i.val)) hg (i.removeNth v))
  apply H.congr
  filter_upwards with x
  symm
  simp only [coordinateJacobian_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tendsto_integral_coordinateJacobian_head_error {n : ℕ} {η u : E → ℝ}
    {us : ℕ → E → ℝ} {gs : ℕ → Fin n → E → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {K : ℝ≥0}
    (hu : LipschitzWith K u) (hus : ∀ j, LipschitzWith K (us j))
    (hgs : ∀ j i, LipschitzWith K (gs j i))
    (hulim : ∀ x, Tendsto (fun j => us j x) atTop (𝓝 (u x)))
    (v : Fin (n+1) → E) :
    Tendsto (fun j => ∫ x, (us j x-u x) * coordinateJacobian (Fin.cons η (gs j)) v x ∂μ)
      atTop (𝓝 0) := by
  classical
  obtain ⟨N, hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hηc hη one_ne_zero
  obtain ⟨B, _, hB⟩ := coordinateJacobian_uniform_bound (max N K) v
  obtain ⟨C, hC0, hC⟩ := uniformly_bounded_lipschitz_on_compact hus (hulim 0) hηc
  have hCu (x : E) (hx : x ∈ tsupport η) : ‖u x‖ ≤ C :=
    le_of_tendsto' (hulim x).norm (fun j => hC j x hx)
  let A := (tsupport η).indicator (fun _ : E => 2*C)
  let as := fun j => (tsupport η).indicator (fun x => us j x-u x)
  have hA : Integrable A μ := (integrable_indicator_iff (isClosed_tsupport η).measurableSet).2
    (continuous_const.continuousOn.integrableOn_compact hηc)
  have ha (j : ℕ) : AEStronglyMeasurable (as j) μ :=
    ((hus j).continuous.sub hu.continuous).aestronglyMeasurable.indicator
      (isClosed_tsupport η).measurableSet
  have haA (j : ℕ) : ∀ᵐ x ∂μ, ‖as j x‖ ≤ A x := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simp only [as, A, indicator_of_mem hx]
      calc ‖us j x-u x‖ ≤ ‖us j x‖ + ‖u x‖ := norm_sub_le _ _
        _ ≤ 2*C := by linarith [hC j x hx, hCu x hx]
    · simp [as, A, hx]
  have halim : ∀ᵐ x ∂μ, Tendsto (fun j => as j x) atTop (𝓝 0) := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · simpa [as, hx] using (hulim x).sub_const (u x)
    · simp [as, hx]
  have hJ (j : ℕ) : ∀ x, ‖coordinateJacobian (Fin.cons η (gs j)) v x‖ ≤ B := by
    apply hB
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hN.weaken (le_max_left _ _)
    · exact (hgs j i).weaken (le_max_right _ _)
  have H := tendsto_integral_mul_uniformly_bounded μ hA ha
    (fun j => (measurable_coordinateJacobian (Fin.cons η (gs j)) v).aestronglyMeasurable)
    haA hJ halim
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport η
  · simp [as, hx]
  · simp [as, hx, coordinateJacobian_cons, fderiv_of_notMem_tsupport ℝ hx]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Jacobian_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma coordinateJacobian_weak_from_smooth {n : ℕ} {fs : ℕ → Fin n → E → ℝ}
    {f : Fin n → E → ℝ} {K : ℝ≥0} (hfs : ∀ j i, LipschitzWith K (fs j i))
    (hf : ∀ i, LipschitzWith K (f i)) (v : Fin n → E)
    (hsm : ∀ η : E → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      Tendsto (fun j => ∫ x, η x * coordinateJacobian (fs j) v x ∂μ) atTop
        (𝓝 (∫ x, η x * coordinateJacobian f v x ∂μ)))
    {a : E → ℝ} (ha : Integrable a μ) :
    Tendsto (fun j => ∫ x, a x * coordinateJacobian (fs j) v x ∂μ) atTop
      (𝓝 (∫ x, a x * coordinateJacobian f v x ∂μ)) := by
  obtain ⟨B, hB0, hB⟩ := coordinateJacobian_uniform_bound K v
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hd : 0 < 4*B+1 := by positivity
  obtain ⟨η, hη, hηc, happrox⟩ := integrable_smooth_compact_L1_approx μ ha (div_pos hε hd)
  have hηI : Integrable η μ := hη.continuous.integrable_of_hasCompactSupport hηc
  have hbε : (ε / (4*B+1))*B < ε/4 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith
  have hdist (q : Fin n → E → ℝ) (hq : ∀ i, LipschitzWith K (q i)) :
      dist (∫ x, a x * coordinateJacobian q v x ∂μ)
        (∫ x, η x * coordinateJacobian q v x ∂μ) < ε/4 := by
    rw [dist_eq_norm]
    exact ((integral_weight_coordinateJacobian_difference_bound μ ha hηI hq v (hB q hq)).trans
      (mul_le_mul_of_nonneg_right happrox hB0)).trans_lt hbε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hsm η hη hηc) (ε/2) (half_pos hε)
  refine ⟨N, fun j hj => ?_⟩
  have H₁ := dist_triangle
    (∫ x, a x * coordinateJacobian (fs j) v x ∂μ)
    (∫ x, η x * coordinateJacobian (fs j) v x ∂μ)
    (∫ x, a x * coordinateJacobian f v x ∂μ)
  have H₂ := dist_triangle
    (∫ x, η x * coordinateJacobian (fs j) v x ∂μ)
    (∫ x, η x * coordinateJacobian f v x ∂μ)
    (∫ x, a x * coordinateJacobian f v x ∂μ)
  have H₃ := hdist (fs j) (hfs j)
  have H₄ := hdist f hf
  rw [dist_comm] at H₄
  have H₅ := hN j hj
  linarith

end CAT0Fillings

namespace CAT0Fillings
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma weak_coordinateJacobian (n : ℕ) :
    ∀ {K : ℝ≥0} {fs : ℕ → Fin n → E → ℝ} {f : Fin n → E → ℝ},
    (∀ j i, LipschitzWith K (fs j i)) → (∀ i, LipschitzWith K (f i)) →
    (∀ i x, Tendsto (fun j => fs j i x) atTop (𝓝 (f i x))) →
    ∀ (v : Fin n → E) {a : E → ℝ}, Integrable a μ →
    Tendsto (fun j => ∫ x, a x * coordinateJacobian (fs j) v x ∂μ) atTop
      (𝓝 (∫ x, a x * coordinateJacobian f v x ∂μ)) := by
  induction n with
  | zero =>
    intro K fs f hfs hf hlim v a ha
    simp [coordinateJacobian]
  | succ n ih =>
    intro K fs f hfs hf hlim v a ha
    apply coordinateJacobian_weak_from_smooth μ hfs hf v ?_ ha
    intro η hη hηc
    have HE := tendsto_integral_coordinateJacobian_head_error μ hη hηc
      (hf 0) (fun j => hfs j 0) (fun j i => hfs j i.succ) (hlim 0) v
    have HF : Tendsto
        (fun j => ∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) atTop
        (𝓝 (∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => f i.succ)) v x ∂μ)) := by
      have heq (j : ℕ) := integral_coordinateJacobian_expand μ (hf 0).continuous hη hηc
        (fun i => hfs j i.succ) v
      have hleq := integral_coordinateJacobian_expand μ (hf 0).continuous hη hηc
        (fun i => hf i.succ) v
      simp_rw [heq, hleq]
      apply tendsto_finsetSum
      intro i _
      exact ih (fun j k => hfs j k.succ) (fun k => hf k.succ) (fun k x => hlim k.succ x)
        (i.removeNth v) (integrable_continuous_mul_compact_fderiv μ
          (hf 0).continuous hη hηc (v i) ((-1 : ℝ)^i.val))
    have heq (j : ℕ) :
        (∫ x, (fs j 0 x-f 0 x) * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) =
        (∫ x, fs j 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) -
        (∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) := by
      simpa only [← sub_mul] using integral_sub
        (integrable_coordinateJacobian_cons_weight μ (hfs j 0).continuous hη hηc
          (fun i => hfs j i.succ) v)
        (integrable_coordinateJacobian_cons_weight μ (hf 0).continuous hη hηc
          (fun i => hfs j i.succ) v)
    simp_rw [heq] at HE
    have HI : Tendsto
        (fun j => ∫ x, fs j 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) atTop
        (𝓝 (∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => f i.succ)) v x ∂μ)) := by
      simpa only [sub_add_cancel, zero_add] using HE.add HF
    have hcons (q : Fin (n+1) → E → ℝ) : Fin.cons (q 0) (fun i => q i.succ) = q := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have hleft (j : ℕ) : (∫ x, η x * coordinateJacobian (fs j) v x ∂μ) =
        -(∫ x, fs j 0 x * coordinateJacobian (Fin.cons η (fun i => fs j i.succ)) v x ∂μ) := by
      simpa only [hcons] using integral_coordinateJacobian_cons μ hη hηc
        (hfs j 0) (fun i => hfs j i.succ) v
    have hright : (∫ x, η x * coordinateJacobian f v x ∂μ) =
        -(∫ x, f 0 x * coordinateJacobian (Fin.cons η (fun i => f i.succ)) v x ∂μ) := by
      simpa only [hcons] using integral_coordinateJacobian_cons μ hη hηc
        (hf 0) (fun i => hf i.succ) v
    simp_rw [hleft, hright]
    exact HI.neg

end CAT0Fillings

open Set Filter Metric
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_CurrentAxioms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma scalar_linear (b c : X → ℝ) (a d : ℝ) :
    C.scalar (fun x => a*b x+d*c x) = fun z => a*C.scalar b z+d*C.scalar c z := by
  funext z
  by_cases hz : z ∈ C.domain <;> simp [scalar,hz]

end CAT0Fillings.IntegerChart

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
lemma abs_det_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le
    (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)))
  rw [Orientation.volumeForm_robust _ b rfl, Module.Basis.det_apply] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have heq : b.toBasis.toMatrix (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))) = A.transpose := by
    ext i j
    simp [b, Module.Basis.toMatrix_apply]
  rw [heq, Matrix.det_transpose]

lemma row_norm_le_of_dot_bound {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_one_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ 1 := by
  apply (abs_det_le_prod_row_norm A).trans
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => row_norm_le_of_dot_bound _ (h i))

lemma row_norm_le_of_dot_bound_const {n : ℕ} (a : Fin n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ K := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_pow_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ K^n := by
  apply (abs_det_le_prod_row_norm A).trans
  calc
    _ ≤ ∏ _i : Fin n, K := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => row_norm_le_of_dot_bound_const _ hK (h i))
    _ = K^n := by simp

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped RealInnerProductSpace MatrixOrder

noncomputable def matrixRowFunctional {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ j, M i j • EuclideanSpace.proj j

@[simp] lemma matrixRowFunctional_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    matrixRowFunctional M i v = M i ⬝ᵥ v := by
  simp [matrixRowFunctional,dotProduct]

@[simp] lemma matrixRowFunctional_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : matrixRowFunctional M i (EuclideanSpace.single j 1) = M i j := by
  simp [dotProduct]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_MeasurePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma restrict_eq_sum_of_ae_partition {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {t : ℕ → Set α}
    (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (t i) (t j))) (hnull : μ (s \ ⋃ i, t i) = 0) :
    μ.restrict s = Measure.sum (fun i => μ.restrict (t i)) := by
  have hsub : (⋃ i, t i) ⊆ s := iUnion_subset hts
  have heq : s =ᵐ[μ] ⋃ i, t i := ae_eq_set.mpr ⟨hnull,by simp only [sdiff_eq_empty.mpr hsub,measure_empty]⟩
  rw [Measure.restrict_congr_set heq,Measure.restrict_iUnion hdisj ht]

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_CurveSpeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiationDense
variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X] {f : ℝ → X} {K : ℝ≥0}
noncomputable def distanceCoordinate (f : ℝ → X) (q : ℕ) (t : ℝ) : ℝ :=
  dist (f t) (denseSeq X q)

noncomputable def metricSpeed (f : ℝ → X) (t : ℝ) : ℝ :=
  ⨆ q : ℕ, |deriv (distanceCoordinate f q) t|

lemma coordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (distanceCoordinate f q) := by
  change LipschitzWith K (fun t : ℝ => dist (f t) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma coordinate_deriv_bound (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ K := by
  simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (coordinate_lipschitz hf q)

lemma coordinate_deriv_le_speed (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ metricSpeed f t :=
  le_ciSup ⟨(K : ℝ), by rintro v ⟨r, rfl⟩; exact coordinate_deriv_bound hf r t⟩ q

lemma metricSpeed_nonneg (hf : LipschitzWith K f) (t : ℝ) : 0 ≤ metricSpeed f t :=
  (abs_nonneg _).trans (coordinate_deriv_le_speed hf 0 t)

lemma metricSpeed_le (hf : LipschitzWith K f) (t : ℝ) : metricSpeed f t ≤ K :=
  ciSup_le (fun q => coordinate_deriv_bound hf q t)

lemma measurable_metricSpeed (f : ℝ → X) : Measurable (metricSpeed f) :=
  Measurable.iSup (fun q => (measurable_deriv (distanceCoordinate f q)).abs)

lemma locallyIntegrable_metricSpeed (hf : LipschitzWith K f) :
    LocallyIntegrable (metricSpeed f) volume := by
  apply (memLp_top_of_bound (measurable_metricSpeed f).aestronglyMeasurable (K : ℝ) ?_).locallyIntegrable le_top
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (metricSpeed_nonneg hf t)]
    exact metricSpeed_le hf t

lemma intervalIntegrable_metricSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    IntervalIntegrable (metricSpeed f) volume s t :=
  intervalIntegrable_iff.mpr
    (((locallyIntegrable_metricSpeed hf).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

lemma coordinate_difference_bound (hf : LipschitzWith K f) (q : ℕ) {s t : ℝ} (hst : s ≤ t) :
    |distanceCoordinate f q t - distanceCoordinate f q s| ≤ ∫ x in s..t, metricSpeed f x := by
  have hac := (coordinate_lipschitz hf q).lipschitzOnWith.absolutelyContinuousOnInterval (a := s) (b := t)
  rw [← hac.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm hst).trans
  apply intervalIntegral.integral_mono_on hst hac.intervalIntegrable_deriv.norm
    (intervalIntegrable_metricSpeed hf s t)
  intro x hx
  exact coordinate_deriv_le_speed hf q x

lemma distance_le_integral_speed (hf : LipschitzWith K f) {s t : ℝ} (hst : s ≤ t) :
    dist (f t) (f s) ≤ ∫ x in s..t, metricSpeed f x := by
  have hc : Continuous (fun y : X => |dist (f t) y - dist (f s) y|) :=
    ((continuous_const.dist continuous_id).sub (continuous_const.dist continuous_id)).abs
  have h := (denseRange_denseSeq X).induction_on
    (p := fun y : X => |dist (f t) y - dist (f s) y| ≤
      ∫ x in s..t, metricSpeed f x) (f s) (isClosed_le hc continuous_const)
      (fun q => coordinate_difference_bound hf q hst)
  simpa using h

noncomputable def integratedSpeed (f : ℝ → X) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, metricSpeed f x

lemma distance_le_integratedSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    dist (f t) (f s) ≤ |integratedSpeed f t - integratedSpeed f s| := by
  have hi (a b : ℝ) := intervalIntegrable_metricSpeed hf a b
  have hd (a b : ℝ) : integratedSpeed f b - integratedSpeed f a =
      ∫ x in a..b, metricSpeed f x := by
    exact intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  rcases le_total s t with hst | hts
  · rw [hd s t, abs_of_nonneg (intervalIntegral.integral_nonneg hst
      (fun x hx => metricSpeed_nonneg hf x))]
    exact distance_le_integral_speed hf hst
  · rw [abs_sub_comm, hd t s, abs_of_nonneg (intervalIntegral.integral_nonneg hts
      (fun x hx => metricSpeed_nonneg hf x)), dist_comm]
    exact distance_le_integral_speed hf hts

def HasMetricDerivAt (f : ℝ → X) (v x : ℝ) : Prop :=
  Tendsto (fun t => dist (f t) (f x) / |t-x|) (𝓝[≠] x) (𝓝 v)

lemma abs_slope_tendsto {g : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt g d x) :
    Tendsto (fun t => |g t-g x|/|t-x|) (𝓝[≠] x) (𝓝 |d|) := by
  simpa only [slope, norm_smul, norm_inv, Real.norm_eq_abs, vsub_eq_sub, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope.norm

theorem ae_hasMetricDerivAt (hf : LipschitzWith K f) :
    ∀ᵐ x, HasMetricDerivAt f (metricSpeed f x) x := by
  have hcoords : ∀ᵐ x, ∀ q : ℕ, DifferentiableAt ℝ (distanceCoordinate f q) x := by
    rw [ae_all_iff]
    intro q
    exact (coordinate_lipschitz hf q).ae_differentiableAt_real
  have hint := LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_metricSpeed hf)
  filter_upwards [hcoords, hint] with x hx hI
  have hg := abs_slope_tendsto (hI 0)
  rw [abs_of_nonneg (metricSpeed_nonneg hf x)] at hg
  change Tendsto (fun t => |integratedSpeed f t-integratedSpeed f x|/|t-x|)
    (𝓝[≠] x) (𝓝 (metricSpeed f x)) at hg
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hb : BddAbove (range (fun q : ℕ => |deriv (distanceCoordinate f q) x|)) :=
      ⟨(K : ℝ), by rintro v ⟨q, rfl⟩; exact coordinate_deriv_bound hf q x⟩
    obtain ⟨q, hq⟩ := (lt_ciSup_iff hb).mp hc
    have hd := abs_slope_tendsto (hx q).hasDerivAt
    filter_upwards [hd.eventually (eventually_gt_nhds hq)] with t ht
    exact ht.trans_le (div_le_div_of_nonneg_right
      (abs_dist_sub_le (f t) (f x) (denseSeq X q)) (abs_nonneg _))
  · intro c hc
    filter_upwards [hg.eventually (eventually_lt_nhds hc)] with t ht
    exact (div_le_div_of_nonneg_right (distance_le_integratedSpeed hf x t) (abs_nonneg _)).trans_lt ht

end CAT0Fillings.MetricDifferentiationDense

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Directional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
variable {X : Type*} [MetricSpace X]
noncomputable def signedDistance (c : ℝ → X) (t : ℝ) : ℝ :=
  if 0 ≤ t then dist (c t) (c 0) else -dist (c t) (c 0)

lemma signedDistance_zero (c : ℝ → X) : signedDistance c 0 = 0 := by
  simp [signedDistance]

lemma signedDistance_div (c : ℝ → X) (t : ℝ) :
    signedDistance c t / t = dist (c t) (c 0) / |t| := by
  rcases le_total 0 t with ht | ht
  · simp [signedDistance, ht, abs_of_nonneg ht]
  · by_cases h0 : t = 0
    · simp [h0]
    · simp [signedDistance, not_le.mpr (lt_of_le_of_ne ht h0), abs_of_nonpos ht, neg_div, div_neg]

lemma hasDerivAt_signedDistance_iff (c : ℝ → X) (d : ℝ) :
    HasDerivAt (signedDistance c) d 0 ↔
      Tendsto (fun t => dist (c t) (c 0) / |t|) (𝓝[≠] 0) (𝓝 d) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, signedDistance_zero, sub_zero, smul_eq_mul, ← div_eq_inv_mul,
    signedDistance_div]

lemma continuous_signedDistance {A : Type*} [TopologicalSpace A] {c : A → ℝ → X}
    (hc : Continuous c.uncurry) : Continuous (fun p : A × ℝ => signedDistance (c p.1) p.2) := by
  have hd : Continuous (fun p : A × ℝ => dist (c p.1 p.2) (c p.1 0)) :=
    hc.dist (hc.comp (continuous_fst.prodMk continuous_const))
  exact hd.if_le hd.neg continuous_const continuous_snd (by
    rintro ⟨x,t⟩ (h : 0 = t)
    simp [← h])

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

noncomputable def scalarCoordinate (f : E → X) (q : ℕ) (x : E) : ℝ :=
  dist (f x) (denseSeq X q)

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
lemma scalarCoordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (scalarCoordinate f q) := by
  change LipschitzWith K (fun x : E => dist (f x) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using
    (LipschitzWith.dist_left (denseSeq X q)).comp hf

noncomputable def lineSpeed (f : E → X) (v x : E) : ℝ :=
  ⨆ q : ℕ, |lineDeriv ℝ (scalarCoordinate f q) x v|

lemma measurable_lineSpeed (hf : Continuous f) (v : E) : Measurable (lineSpeed f v) := by
  apply Measurable.iSup
  intro q
  exact (measurable_lineDeriv (hf.dist continuous_const)).abs

omit [MeasurableSpace E] [BorelSpace E] in
lemma deriv_coordinate_line (p v : E) (s : ℝ) (q : ℕ) :
    deriv (MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q) s =
      lineDeriv ℝ (scalarCoordinate f q) (p+s • v) v := by
  rw [lineDeriv]
  have he : (fun t : ℝ => scalarCoordinate f q (p+s • v+t • v)) =
      (fun t : ℝ => MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q (s+t)) := by
    ext t
    simp [scalarCoordinate, MetricDifferentiationDense.distanceCoordinate, add_smul, add_assoc]
  rw [he]
  simpa using (deriv_comp_const_add (f := MetricDifferentiationDense.distanceCoordinate
    (fun t => f (p+t • v)) q) s 0).symm

omit [MeasurableSpace E] [BorelSpace E] in
lemma lineSpeed_eq_curveSpeed (p v : E) (s : ℝ) :
    lineSpeed f v (p+s • v) = MetricDifferentiationDense.metricSpeed (fun t => f (p+t • v)) s := by
  simp only [lineSpeed, MetricDifferentiationDense.metricSpeed, deriv_coordinate_line]

lemma measurableSet_hasMetricDirectionalDeriv (hf : Continuous f) (v : E) :
    MeasurableSet {x | Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x))} := by
  let c : E → ℝ → X := fun x t => f (x + t • v)
  have hc : Continuous c.uncurry := hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hD := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => signedDistance (c x) t) (continuous_signedDistance hc)
  have hder := measurable_deriv_with_param (f := fun x t => signedDistance (c x) t)
    (continuous_signedDistance hc)
  have hm := (measurable_prodMk_right (y := (0 : ℝ)) hD).inter
    (measurableSet_eq_fun (hder.comp (measurable_prodMk_right (y := (0 : ℝ)))) (measurable_lineSpeed hf v))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro ht
    have hd := (hasDerivAt_signedDistance_iff (c x) (lineSpeed f v x)).mpr (by simpa [c] using ht)
    exact ⟨hd.differentiableAt, hd.deriv⟩
  · rintro ⟨hd, he⟩
    rw [← he]
    simpa [c] using (hasDerivAt_signedDistance_iff (c x) _).mp hd.hasDerivAt

lemma tendsto_add_zero_punctured (s : ℝ) :
    Tendsto (fun t : ℝ => s+t) (𝓝[≠] 0) (𝓝[≠] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => s) (𝓝 0) (𝓝 s)).add tendsto_id).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

theorem ae_hasMetricDirectionalDeriv [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x)) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  apply ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
    (measurableSet_hasMetricDirectionalDeriv hf.continuous v)
  intro p
  have hcurve := hf.comp ((LipschitzWith.const p).add L.lipschitz)
  filter_upwards [MetricDifferentiationDense.ae_hasMetricDerivAt hcurve] with s hs
  change Tendsto (fun t : ℝ => dist (f (p+s • v+t • v)) (f (p+s • v)) / |t|)
    (𝓝[≠] 0) (𝓝 (lineSpeed f v (p+s • v)))
  rw [lineSpeed_eq_curveSpeed]
  have hh := hs.comp (tendsto_add_zero_punctured s)
  simpa only [Function.comp_def, L, MetricDifferentiationDense.HasMetricDerivAt,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    add_smul, add_assoc, add_sub_cancel_left] using hh

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Seminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
noncomputable def coordinateSeminorm (f : E → X) (x : E) (q : ℕ) : Seminorm ℝ E :=
  (normSeminorm ℝ ℝ).comp (fderiv ℝ (scalarCoordinate f q) x).toLinearMap

lemma coordinateSeminorm_le (hf : LipschitzWith K f) (x : E) (q : ℕ) :
    coordinateSeminorm f x q ≤ K • normSeminorm ℝ E := by
  intro v
  change ‖fderiv ℝ (scalarCoordinate f q) x v‖ ≤ (K : ℝ) * ‖v‖
  exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ (scalarCoordinate_lipschitz hf q)) (norm_nonneg _))

noncomputable def metricSeminorm (f : E → X) (x : E) : Seminorm ℝ E :=
  ⨆ q : ℕ, coordinateSeminorm f x q

lemma bddAbove_coordinateSeminorm (hf : LipschitzWith K f) (x : E) :
    BddAbove (range (coordinateSeminorm f x)) :=
  ⟨K • normSeminorm ℝ E, by rintro p ⟨q,rfl⟩; exact coordinateSeminorm_le hf x q⟩

lemma metricSeminorm_apply (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v = ⨆ q : ℕ, |fderiv ℝ (scalarCoordinate f q) x v| := by
  rw [metricSeminorm, Seminorm.iSup_apply (bddAbove_coordinateSeminorm hf x)]
  rfl

lemma metricSeminorm_le (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v ≤ (K : ℝ) * ‖v‖ :=
  (ciSup_le (fun q => coordinateSeminorm_le hf x q) :
    metricSeminorm f x ≤ K • normSeminorm ℝ E) v

lemma metricSeminorm_lipschitz (hf : LipschitzWith K f) (x : E) :
    LipschitzWith K (metricSeminorm f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
  exact ((metricSeminorm f x).norm_sub_map_le_sub v w).trans (metricSeminorm_le hf x (v-w))

lemma lineSpeed_eq_metricSeminorm (hf : LipschitzWith K f) {x : E}
    (hx : ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x) (v : E) :
    lineSpeed f v x = metricSeminorm f x v := by
  rw [metricSeminorm_apply hf]
  simp only [lineSpeed, (hx _).lineDeriv_eq_fderiv]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ae_dense_directionalSeminorm (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (metricSeminorm f x (denseSeq E j))) := by
  have hcoord : ∀ᵐ x ∂μ, ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x := by
    rw [ae_all_iff]
    exact fun q => (scalarCoordinate_lipschitz hf q).ae_differentiableAt
  have hdir : ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (lineSpeed f (denseSeq E j) x)) := by
    rw [ae_all_iff]
    exact fun j => ae_hasMetricDirectionalDeriv μ hf _
  filter_upwards [hcoord, hdir] with x hx hd j
  simpa only [lineSpeed_eq_metricSeminorm hf hx] using hd j

end CAT0Fillings.MetricDifferentiation

open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings
open Metric

lemma uniformly_tendsto_of_lipschitz {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {s : Set A} (hs : IsCompact s)
    (hlim : ∀ x ∈ s, Tendsto (fun j => f j x) l (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ x ∈ s, dist (f j x) (g x) < ε := by
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, hts, ht, hcov⟩ := hs.finite_cover_balls hδ
  have hev : ∀ᶠ j in l, ∀ y ∈ t, dist (f j y) (g y) < ε/2 := by
    rw [ht.eventually_all]
    exact fun y hy => (Metric.tendsto_nhds.mp (hlim y (hts hy))) (ε/2) (half_pos hε)
  filter_upwards [hev] with j hj x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, dist x y < δ := by
    rcases mem_iUnion.mp (hcov hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hball⟩
    exact ⟨y, hyt, hball⟩
  have hdr : (K : ℝ) * dist x y < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hxy (show 0 < (K : ℝ)+1 by positivity)
    have heq : ((K : ℝ)+1)*δ = ε/4 := by dsimp [δ]; field_simp
    rw [heq] at hm
    exact lt_of_le_of_lt (by nlinarith [dist_nonneg (x := x) (y := y)]) hm
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j y) + dist (f j y) (g y) + dist (g y) (g x) :=
        (dist_triangle _ (g y) _).trans (add_le_add (dist_triangle _ (f j y) _) le_rfl)
    _ < ε/4 + ε/2 + ε/4 := by
      apply add_lt_add
      · exact add_lt_add (((hf j).dist_le_mul x y).trans_lt hdr) (hj y hy)
      · rw [dist_comm]
        exact (hg.dist_le_mul x y).trans_lt hdr
    _ = ε := by ring
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Centered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}
noncomputable def metricQuotient (f : E → X) (x : E) (t : ℝ) (v : E) : ℝ :=
  dist (f (x+t • v)) (f x) / |t|

lemma metricQuotient_lipschitz (hf : LipschitzWith K f) (x : E) (t : ℝ) :
    LipschitzWith K (metricQuotient f x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  by_cases ht : t = 0
  · simp only [metricQuotient, ht, abs_zero, div_zero, dist_self]
    positivity
  have ht' : 0 < |t| := abs_pos.mpr ht
  simp only [metricQuotient, Real.dist_eq, ← sub_div, abs_div, abs_abs]
  calc |dist (f (x+t • v)) (f x) - dist (f (x+t • w)) (f x)|/|t| ≤
        dist (f (x+t • v)) (f (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (abs_dist_sub_le _ _ _) ht'.le
    _ ≤ ((K : ℝ) * dist (x+t • v) (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (hf.dist_le_mul _ _) ht'.le
    _ = (K : ℝ) * dist v w := by
      rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, dist_eq_norm]
      field_simp

def HasCenteredMetricDifferential (f : E → X) (p : Seminorm ℝ E) (x : E) : Prop :=
  (fun y => dist (f y) (f x) - p (y-x)) =o[𝓝 x] (fun y => y-x)

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_ErrorModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
omit [FiniteDimensional ℝ E] in
lemma measurable_metricSeminorm_apply (hf : LipschitzWith K f) (v : E) :
    Measurable (fun x => metricSeminorm f x v) := by
  simp only [metricSeminorm_apply hf]
  exact Measurable.iSup (fun q => (measurable_fderiv_apply_const ℝ (scalarCoordinate f q) v).abs)

noncomputable def metricErrorTerm (f : E → X) (r : ℝ) (q : ℕ) (x : E) : ℝ :=
  if 0 < ‖denseSeq E q‖ ∧ ‖denseSeq E q‖ ≤ r then
    |dist (f (x + denseSeq E q)) (f x) - metricSeminorm f x (denseSeq E q)| / ‖denseSeq E q‖
  else 0

noncomputable def metricErrorModulus (f : E → X) (r : ℝ) (x : E) : ℝ :=
  ⨆ q : ℕ, metricErrorTerm f r q x

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_nonneg (r : ℝ) (q : ℕ) (x : E) :
    0 ≤ metricErrorTerm f r q x := by
  dsimp [metricErrorTerm]
  split_ifs
  · positivity
  · rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_le (hf : LipschitzWith K f) (r : ℝ) (q : ℕ) (x : E) :
    metricErrorTerm f r q x ≤ 2*(K : ℝ) := by
  dsimp [metricErrorTerm]
  split_ifs with h
  · apply (div_le_iff₀ h.1).mpr
    have hd : dist (f (x+denseSeq E q)) (f x) ≤ (K : ℝ)*‖denseSeq E q‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hf.dist_le_mul (x+denseSeq E q) x
    have hp := metricSeminorm_le hf x (denseSeq E q)
    have hp0 := apply_nonneg (metricSeminorm f x) (denseSeq E q)
    have hd0 := dist_nonneg (x := f (x+denseSeq E q)) (y := f x)
    rw [abs_le]
    constructor <;> nlinarith
  · positivity

omit [MeasurableSpace E] [BorelSpace E] in
lemma bddAbove_metricErrorTerm (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    BddAbove (range (fun q => metricErrorTerm f r q x)) :=
  ⟨2*(K : ℝ), by rintro _ ⟨q,rfl⟩; exact metricErrorTerm_le hf r q x⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_nonneg (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    0 ≤ metricErrorModulus f r x :=
  (metricErrorTerm_nonneg r 0 x).trans (le_ciSup (bddAbove_metricErrorTerm hf r x) 0)

lemma measurable_metricErrorModulus (hf : LipschitzWith K f) (r : ℝ) :
    Measurable (metricErrorModulus f r) := by
  change Measurable (fun x => ⨆ q : ℕ, metricErrorTerm f r q x)
  apply Measurable.iSup
  intro q
  change Measurable (fun x => metricErrorTerm f r q x)
  unfold metricErrorTerm
  split_ifs
  · exact (((hf.continuous.comp (continuous_id.add continuous_const)).dist hf.continuous).measurable.sub
      (measurable_metricSeminorm_apply hf _)).abs.div_const _
  · exact measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_le_of_bound (_hf : LipschitzWith K f) {r ε : ℝ} {x : E}
    (hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ ≤ r → |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ ε*‖v‖) :
    metricErrorModulus f r x ≤ ε := by
  apply ciSup_le
  intro q
  dsimp [metricErrorTerm]
  split_ifs with h
  · exact (div_le_iff₀ h.1).mpr (H _ h.2)
  · exact hε

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_tendsto_zero (hf : LipschitzWith K f) {x : E}
    (hx : HasCenteredMetricDifferential f (metricSeminorm f x) x)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (metricErrorModulus_nonneg hf _ _))
  · intro ε hε
    have hxε := hx.bound (half_pos hε)
    obtain ⟨δ,hδ,hδx⟩ := Metric.mem_nhds_iff.mp hxε
    have hδr := (tendsto_order.1 hr).2 δ hδ
    filter_upwards [hδr] with n hn
    apply lt_of_le_of_lt (metricErrorModulus_le_of_bound hf (half_pos hε).le ?_)
      (half_lt_self hε)
    intro v hv
    have hvδ : x+v ∈ ball x δ := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hv.trans_lt hn
    simpa only [mem_ofPred_eq, add_sub_cancel_left, Real.norm_eq_abs] using hδx hvδ

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_TwoPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma seminorm_sub_bound_of_sphere {p q : Seminorm ℝ E} {ε : ℝ} (_hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ = 1 → |p v-q v| ≤ ε) (v : E) :
    |p v-q v| ≤ ε*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,hv0.ne']
  have he : ‖v‖ • u = v := by simp [u,hv0.ne']
  have hpv : p v = ‖v‖ * p u := by
    calc p v = p (‖v‖ • u) := congrArg p he.symm
      _ = ‖v‖ * p u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  have hqv : q v = ‖v‖ * q u := by
    calc q v = q (‖v‖ • u) := congrArg q he.symm
      _ = ‖v‖ * q u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  calc |p v-q v| = ‖v‖ * |p u-q u| := by
        rw [hpv,hqv,←mul_sub,abs_mul,abs_of_pos hv0]
    _ ≤ ‖v‖*ε := mul_le_mul_of_nonneg_left (H u hu) hv0.le
    _ = ε*‖v‖ := mul_comm _ _

variable [FiniteDimensional ℝ E]

variable {X : Type*} [MetricSpace X]

def HasTwoPointMetricDifferential (f : E → X) (p : Seminorm ℝ E)
    (s : Set E) (x : E) : Prop :=
  (fun q : E × E => dist (f q.1) (f q.2) - p (q.1 - q.2)) =o[𝓝[s ×ˢ s] (x, x)]
    (fun q : E × E => ‖q.1 - x‖ + ‖q.2 - x‖)

end CAT0Fillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_LargePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings
lemma exists_closed_large_continuousOn
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {f : A → B} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set A, IsClosed K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  let I := countableBasis B
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε I
  have H (i : I) : ∃ U F : Set A,
      f ⁻¹' (i : Set B) ⊆ U ∧ F ⊆ f ⁻¹' (i : Set B) ∧
      IsOpen U ∧ IsClosed F ∧ μ (U \ F) < δ i := by
    let S := f ⁻¹' (i : Set B)
    have hS : MeasurableSet S := hf (isOpen_of_mem_countableBasis i.property).measurableSet
    have hδi : δ i / 2 ≠ 0 := (ENNReal.half_pos (hδ i).ne').ne'
    obtain ⟨U,hSU,hU,_,hμU⟩ := hS.exists_isOpen_sdiff_lt (measure_ne_top μ S) hδi
    obtain ⟨F,hFS,hF,hμF⟩ := hS.exists_isClosed_sdiff_lt (measure_ne_top μ S) hδi
    refine ⟨U,F,hSU,hFS,hU,hF,?_⟩
    calc μ (U \ F) ≤ μ ((U \ S) ∪ (S \ F)) := by
          apply measure_mono
          intro x hx
          by_cases hxs : x ∈ S
          · exact Or.inr ⟨hxs,hx.2⟩
          · exact Or.inl ⟨hx.1,hxs⟩
      _ ≤ μ (U \ S) + μ (S \ F) := measure_union_le _ _
      _ < δ i / 2 + δ i / 2 := ENNReal.add_lt_add hμU hμF
      _ = δ i := ENNReal.add_halves _
  choose U F hSU hFS hU hF hμ using H
  let K : Set A := (⋃ i : I, U i \ F i)ᶜ
  refine ⟨K, (isOpen_iUnion (fun i => (hU i).sdiff (hF i))).isClosed_compl, ?_, ?_⟩
  · calc μ Kᶜ = μ (⋃ i : I, U i \ F i) := by simp [K]
      _ ≤ ∑' i : I, μ (U i \ F i) := measure_iUnion_le _
      _ ≤ ∑' i : I, δ i := ENNReal.tsum_le_tsum (fun i => (hμ i).le)
      _ < ε := hδsum
  · apply (isBasis_countableBasis B).continuousOn_iff.mpr
    intro V hV
    let i : I := ⟨V,hV⟩
    refine ⟨U i,hU i,?_⟩
    ext x
    constructor
    · rintro ⟨hx,hxK⟩
      exact ⟨hSU i hx,hxK⟩
    · rintro ⟨hxU,hxK⟩
      have hxF : x ∈ F i := by
        by_contra h
        exact hxK (mem_iUnion.mpr ⟨i,hxU,h⟩)
      exact ⟨hFS i hxF,hxK⟩


open Metric

lemma exists_large_continuousOn_uniformly
    {A B : Type*} [TopologicalSpace A] [PseudoMetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A)
    {s : Set A} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {f : A → B} (hf : Measurable f) {u : ℕ → A → ℝ}
    (hu : ∀ n, Measurable (u n))
    (hc : ∀ᵐ x ∂μ.restrict s, Tendsto (fun n => u n x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ContinuousOn f t ∧ TendstoUniformlyOn u (fun _ => 0) atTop t := by
  let ν := μ.restrict s
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hsf.lt_top⟩
  obtain ⟨K,hK,hμK,hcf⟩ := exists_closed_large_continuousOn ν hf
    (show ENNReal.ofReal (ε/2) ≠ 0 from (ENNReal.ofReal_pos.mpr (half_pos hε)).ne')
  obtain ⟨e,he,hμe,hue⟩ := tendstoUniformlyOn_of_ae_tendsto'
    (fun n => (hu n).stronglyMeasurable) stronglyMeasurable_const hc
      (half_pos hε)
  let t := s ∩ (K \ e)
  refine ⟨t,inter_subset_left,hs.inter (hK.measurableSet.diff he),?_,
    hcf.mono (fun _ h => h.2.1),hue.mono (fun _ h => h.2.2)⟩
  calc μ (s \ t) = ν (Kᶜ ∪ e) := by
        rw [Measure.restrict_apply (hK.measurableSet.compl.union he)]
        congr 1
        ext x
        simp only [t,Set.mem_sdiff,mem_inter_iff,mem_union,mem_compl_iff]
        tauto
    _ ≤ ν Kᶜ + ν e := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hμK.le hμe
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma tangentConeAt_pi_eq_univ_of_density_one {ι : Type*} [Fintype ι]
    (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    tangentConeAt ℝ {f : ι → E | ∀ i, f i ∈ s} (fun _ => x) = univ := by
  classical
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ i, (s ∩ ({x} + r • closedBall (z i) (ε / 2))).Nonempty := by
    rw [eventually_all]
    intro i
    exact Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _
      measurableSet_closedBall (measure_closedBall_pos μ (z i) (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : ι → E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, hr₁, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  have H (i : ι) : ∃ a ∈ closedBall (z i) (ε / 2), x + r • a ∈ s := by
    obtain ⟨y, hys, hy⟩ := hr₁ i
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    simpa only [h, add_neg_cancel_left] using hys
  choose a ha has using H
  have haz : a ∈ closedBall z (ε / 2) := by
    rw [mem_closedBall, dist_pi_le_iff (half_pos hε).le]
    exact ha
  refine ⟨a, ?_, ?_⟩
  · have hra : r • a ∈ U ∩ ((fun _ : ι => x) + ·) ⁻¹' {f | ∀ i, f i ∈ s} := by
      exact ⟨hrU (smul_mem_smul_set haz), has⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ (ne_of_gt hr) a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using haz) (half_lt_self hε)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u

theorem IsCAT0.exists_squared_distance_convex
    {X : Type u} [MetricSpace X] (hX : IsCAT0 X) :
    ∃ segment : X → X → ℝ → X,
      (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
      ∀ o y x t, t ∈ Icc (0 : ℝ) 1 →
        dist (segment o y t) x ^ 2 ≤
          (1 - t) * dist o x ^ 2 + t * dist y x ^ 2 -
            t * (1 - t) * dist o y ^ 2 := by
  obtain ⟨s, hs, _, hc⟩ := hX
  refine ⟨s, hs, ?_⟩
  intro o y x t ht
  have h := hc o y x t 1 ht (by simp)
  rw [(hs o x).2] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem IsCAT0.quadrilateral {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  obtain ⟨s, _, hs⟩ := hX.exists_squared_distance_convex
  have hb := hs a c b (1 / 2) (by norm_num)
  have hd := hs a c d (1 / 2) (by norm_num)
  have ht := dist_triangle b (s a c (1 / 2)) d
  have ht' : dist b d ^ 2 ≤
      (dist b (s a c (1 / 2)) + dist (s a c (1 / 2)) d) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr ht
  have hm := sq_nonneg (dist b (s a c (1 / 2)) - dist (s a c (1 / 2)) d)
  rw [dist_comm c b] at hb
  rw [dist_comm a d] at hd
  rw [dist_comm b (s a c (1 / 2))] at ht' hm
  nlinarith

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_HilbertCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
lemma ae_restrict_of_arbitrarily_large_pieces
    {A : Type*} [MeasurableSpace A] (μ : Measure A) {s : Set A} (hs : MeasurableSet s)
    {P : A → Prop}
    (H : ∀ ε : ℝ, 0 < ε → ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ᵐ x ∂μ.restrict t, P x) :
    ∀ᵐ x ∂μ.restrict s, P x := by
  apply (ae_restrict_iff' hs).2
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨t,_,ht,htμ,hP⟩ := H ε hε
  have hnull : μ {x | ¬(x ∈ t → P x)} = 0 := ae_iff.1 ((ae_restrict_iff' ht).1 hP)
  calc μ {x | ¬(x ∈ s → P x)} ≤ μ ((s \ t) ∪ {x | ¬(x ∈ t → P x)}) := by
        apply measure_mono
        intro x hx
        simp only [mem_ofPred_eq, Classical.not_imp] at hx
        by_cases hxt : x ∈ t
        · exact Or.inr (by simpa only [mem_ofPred_eq, Classical.not_imp] using And.intro hxt hx.2)
        · exact Or.inl ⟨hx.1,hxt⟩
    _ ≤ μ (s \ t) + μ {x | ¬(x ∈ t → P x)} := measure_union_le _ _
    _ ≤ 0+(ε : ENNReal) := by simpa only [hnull,add_zero,zero_add,ENNReal.ofReal_coe_nnreal] using htμ
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_HilbertMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma measure_le_of_nearIsometry_factors {β : Type*} [MeasurableSpace β]
    {μ ν : Measure β} [IsFiniteMeasure ν] (k : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      μ ≤ ENNReal.ofReal (((1+ε)/(1-ε))^k) • ν) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1+ε)/(1-ε))^k))
      (𝓝[>] 0) (𝓝 1) := by
    have hd : ContinuousAt (fun ε : ℝ => ((1+ε)/(1-ε))^k) 0 := by
      fun_prop (disch := norm_num)
    have hh := ENNReal.continuous_ofReal.continuousAt.comp (x := 0) hd
    simpa only [Function.comp_def,add_zero,sub_zero,div_one,one_pow,ENNReal.ofReal_one] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1+ε)/(1-ε))^k)*ν s)
      (𝓝[>] 0) (𝓝 (ν s)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr (measure_ne_top ν s))
  apply ge_of_tendsto hv
  have hε0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hε1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hε0,hε1] with ε hε hε'
  simpa only [Measure.smul_apply,smul_eq_mul] using h ε hε hε' s

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

noncomputable def coordinateEmptyChart : IntegerChart X k where
  domain := ∅
  borel := MeasurableSet.empty
  bounded := Bornology.isBounded_empty
  param := fun z => False.elim z.property
  bilipschitz := by
    refine ⟨0,0,?_,?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact False.elim a.property
    · intro a b
      exact False.elim a.property
  multiplicity := fun _ => 0
  integrable := by simp

end CAT0Fillings.IntegerChart
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
noncomputable def coordinateMinor (π : Fin k → X → ℝ) (w : Euc (k+1)) : ℝ :=
  (Matrix.of fun i j : Fin k =>
    (fderivWithin ℝ (C.scalar (π i)) C.domain w) (EuclideanSpace.single j.succ 1)).det

end CAT0Fillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Straightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace EuclideanStraightening
variable {d : ℕ}

lemma det_updateRow_one (j : Fin d) (v : Fin d → ℝ) :
    (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j v).det = v j := by
  have he : (∑ i : Fin d, v i • (1 : Matrix (Fin d) (Fin d) ℝ) i) = v := by
    ext l
    simp [Matrix.one_apply]
  rw [←he,Matrix.det_updateRow_sum]
  simp [Matrix.one_apply]

end EuclideanStraightening
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Degenerate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X]
lemma det_rows_eq_zero_of_seminorm_kernel {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hL : ∀ i, ∃ K : ℝ, ∀ v, |L i v| ≤ K*p v)
    (hker : ¬ ∀ v, p v = 0 → v = 0) :
    Matrix.det (fun i j => L i (EuclideanSpace.single j 1)) = 0 := by
  classical
  push Not at hker
  obtain ⟨v,hpv,hv⟩ := hker
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun j => v j,?_,?_⟩
  · intro h
    apply hv
    ext j
    simpa using congrFun h j
  · ext i
    obtain ⟨K,hK⟩ := hL i
    have hLv : L i v = 0 := by
      apply abs_nonpos_iff.mp
      simpa only [hpv,mul_zero] using hK v
    have hsum : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = v := by
      simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    have hli := congrArg (L i) hsum
    rw [_root_.map_sum] at hli
    simp only [map_smul,smul_eq_mul] at hli
    change ∑ j, L i (EuclideanSpace.single j 1) * v j = 0
    simpa only [mul_comm,hLv] using hli

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_FullRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma exists_nat_lower_bound_iff {p : Seminorm ℝ E} (hp : Continuous p) :
    (∃ n : ℕ, ∀ v : E, ‖v‖ ≤ ((n : ℝ)+1)*p v) ↔ ∀ v, p v = 0 → v = 0 := by
  constructor
  · rintro ⟨n,hn⟩ v hv
    have := hn v
    rw [hv,mul_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg v))
  · intro hp0
    by_cases hE : Subsingleton E
    · exact ⟨0, fun v => by simp [Subsingleton.elim v 0]⟩
    let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    obtain ⟨v,hv⟩ := exists_ne (0 : E)
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hs : (Metric.sphere (0 : E) 1).Nonempty := by
      refine ⟨‖v‖⁻¹ • v,?_⟩
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
    obtain ⟨w,hw,hwmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hp.continuousOn
    have hwnorm : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hwnorm
    have hpw : 0 < p w := lt_of_le_of_ne (apply_nonneg p w) (by
      intro h; exact hw0 (hp0 w h.symm))
    obtain ⟨n,hn⟩ := exists_nat_gt (1 / p w)
    refine ⟨n,fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzunit : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hznorm,inv_mul_cancel₀ hznorm.ne']
    have hmin : p w ≤ p (‖z‖⁻¹ • z) := hwmin hzunit
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hznorm] at hmin
    have hn' : 1 ≤ ((n : ℝ)+1)*p w := by
      have hh : 1 < (n : ℝ)*p w := (div_lt_iff₀ hpw).mp hn
      nlinarith
    calc ‖z‖ = ‖z‖*1 := (mul_one _).symm
      _ ≤ ‖z‖*(((n : ℝ)+1)*p w) := mul_le_mul_of_nonneg_left hn' (norm_nonneg z)
      _ ≤ ‖z‖*(((n : ℝ)+1)*(‖z‖⁻¹*p z)) := by
        gcongr
      _ = ((n : ℝ)+1)*p z := by field_simp

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma measurableSet_metricSeminorm_lower_bound (hf : LipschitzWith K f) (A : ℝ) :
    MeasurableSet {x : E | ∀ v : E, ‖v‖ ≤ A * metricSeminorm f x v} := by
  have heq : {x : E | ∀ v : E, ‖v‖ ≤ A * metricSeminorm f x v} =
      ⋂ i : ℕ, {x : E | ‖denseSeq E i‖ ≤ A * metricSeminorm f x (denseSeq E i)} := by
    ext x
    simp only [mem_ofPred_eq,mem_iInter]
    constructor
    · exact fun h i => h _
    · intro h v
      exact (denseRange_denseSeq E).induction_on v
        (isClosed_le continuous_norm ((metricSeminorm_lipschitz hf x).continuous.const_mul A)) h
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le measurable_const ((measurable_metricSeminorm_apply hf _).const_mul A)

end CAT0Fillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Negation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

namespace IntegerChart
variable (C : IntegerChart X k)
noncomputable def negate : IntegerChart X k :=
  { C with multiplicity := fun z => -C.multiplicity z
           integrable := C.integrable.neg.congr (Eventually.of_forall fun _z => (Int.cast_neg _).symm) }

end IntegerChart

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeakMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma integral_continuousMap_lipschitz (μ : FiniteMeasure X) (M : ℝ≥0) (hM : μ.mass ≤ M) :
    LipschitzWith M (fun f : C(X,ℝ) => ∫ x, f x ∂(μ : Measure X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hfi : Integrable (fun x => f x) (μ : Measure X) := (BoundedContinuousFunction.mkOfCompact f).integrable _
  have hgi : Integrable (fun x => g x) (μ : Measure X) := (BoundedContinuousFunction.mkOfCompact g).integrable _
  rw [dist_eq_norm,←integral_sub hfi hgi]
  have hi := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
    (Eventually.of_forall fun x => (f-g).norm_coe_le_norm x)
  have hm : (μ : Measure X).real univ ≤ (M : ℝ) := NNReal.coe_le_coe.mpr hM
  exact hi.trans (by rw [dist_eq_norm]; nlinarith [norm_nonneg (f-g)])

end CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma ae_exists_bounded_subsequence_of_integral_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {G : ℕ → A → ℝ} (hG : ∀ j, Integrable (G j) μ)
    (hG0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ G j x) (M : ℝ) (hM : ∀ j, (∫ x, G j x ∂μ) ≤ M) :
    ∀ᵐ x ∂μ, ∃ C : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, G (ψ j) x ≤ C := by
  let hmeas (j : ℕ) := (hG j).aemeasurable.ennreal_ofReal
  let f (j : ℕ) : A → ℝ≥0∞ := (hmeas j).mk _
  have hf (j : ℕ) : Measurable (f j) := (hmeas j).measurable_mk
  have heq (j : ℕ) : (fun x => ENNReal.ofReal (G j x)) =ᵐ[μ] f j := (hmeas j).ae_eq_mk
  have hI (j : ℕ) : (∫⁻ x, f j x ∂μ) ≤ ENNReal.ofReal M := by
    rw [←lintegral_congr_ae (heq j),←ofReal_integral_eq_lintegral_ofReal (hG j) (hG0 j)]
    exact ENNReal.ofReal_le_ofReal (hM j)
  have hfat : (∫⁻ x, liminf (fun j => f j x) atTop ∂μ) < (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt (lintegral_liminf_le hf)
    exact lt_of_le_of_lt (liminf_le_of_frequently_le (Frequently.of_forall hI)) ENNReal.ofReal_lt_top
  have ha := ae_lt_top (Measurable.liminf hf) hfat.ne
  filter_upwards [ha,ae_all_iff.mpr heq] with x hx he
  obtain ⟨N,hN⟩ := ENNReal.exists_nat_gt hx.ne
  obtain ⟨ψ,hψ,hψbound⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_liminf_lt (u := fun j => f j x) (f := atTop) (h := hN))
  refine ⟨N,ψ,hψ,fun j => ?_⟩
  have hj : ENNReal.ofReal (G (ψ j) x) ≤ ENNReal.ofReal (N:ℝ) := by
    rw [he,ENNReal.ofReal_natCast]
    exact (hψbound j).le
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg N)).mp hj

end CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_NormalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma exists_integrable_subsequence_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {G : ℕ → A → ℝ} (hG : ∀ j, Integrable (G j) μ)
    (hG0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ G j x) (M : ℝ) (hM : ∀ j, (∫ x, G j x ∂μ) ≤ M) :
    ∃ g : A → ℝ, Integrable g μ ∧ (∀ x, 0 ≤ g x) ∧
      (∫ x, g x ∂μ) ≤ max M 0 ∧
      ∀ᵐ x ∂μ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, G (ψ j) x < g x + 1 := by
  let hm (j : ℕ) := (hG j).aemeasurable.ennreal_ofReal
  let f (j : ℕ) : A → ℝ≥0∞ := (hm j).mk _
  have hf (j : ℕ) : Measurable (f j) := (hm j).measurable_mk
  have heq (j : ℕ) : (fun x => ENNReal.ofReal (G j x)) =ᵐ[μ] f j := (hm j).ae_eq_mk
  let H : A → ℝ≥0∞ := fun x => liminf (fun j => f j x) atTop
  have hHm : Measurable H := Measurable.liminf hf
  have hI (j : ℕ) : (∫⁻ x, f j x ∂μ) ≤ ENNReal.ofReal M := by
    rw [←lintegral_congr_ae (heq j),←ofReal_integral_eq_lintegral_ofReal (hG j) (hG0 j)]
    exact ENNReal.ofReal_le_ofReal (hM j)
  have hHI : (∫⁻ x, H x ∂μ) ≤ ENNReal.ofReal M :=
    (lintegral_liminf_le hf).trans (liminf_le_of_frequently_le (Frequently.of_forall hI))
  have hHfin : (∫⁻ x, H x ∂μ) ≠ ⊤ := (hHI.trans_lt ENNReal.ofReal_lt_top).ne
  have hafin := ae_lt_top hHm hHfin
  refine ⟨fun x => (H x).toReal, integrable_toReal_of_lintegral_ne_top hHm.aemeasurable hHfin,
    fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [integral_toReal hHm.aemeasurable hafin]
    simpa only [ENNReal.toReal_ofReal'] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hHI
  · filter_upwards [hafin,ae_all_iff.mpr heq] with x hx he
    have hl : H x < ENNReal.ofReal ((H x).toReal + 1) :=
      (ENNReal.lt_ofReal_iff_toReal_lt hx.ne).mpr (by linarith)
    obtain ⟨ψ,hψ,hψb⟩ := extraction_of_frequently_atTop
      (frequently_lt_of_liminf_lt (u := fun j => f j x) (f := atTop) (h := hl))
    refine ⟨ψ,hψ,fun j => ?_⟩
    have hh : ENNReal.ofReal (G (ψ j) x) < ENNReal.ofReal ((H x).toReal + 1) := by
      rw [he]
      exact hψb j
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hh

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_Poincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {ν : Measure E} [IsFiniteMeasure ν]

def DirectionalVariation (f : E → ℝ) (v : E) (μ ν : Measure E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    |∫ x, (fderiv ℝ φ x) v * f x ∂μ| ≤ ∫ x, |φ x| ∂ν

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal Pointwise

noncomputable section
namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

def halfMean (g : E → ℝ) (x y : E) : ℝ :=
  ∫ t in Icc (0:ℝ) (1/2), g ((1-t) • x+t • y)

end CAT0Fillings.JointBV

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_Oscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

def LocalMeanBound (f : E → ℝ) (A : ℝ) (x : E) (R : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r ≤ R →
    (∫ z in closedBall x r, |f z - (⨍ w in closedBall x r, f w ∂μ)| ∂μ) ≤
      A * r * μ.real (closedBall x r)

end Euclidean
end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
variable {Y : Type*} [MetricSpace Y] [SeparableSpace Y] [Nonempty Y]

noncomputable def metricCone (φ : Y → ℝ) (K : ℝ≥0) (q : Y) (x : Y) : ℝ :=
  φ q + (K : ℝ)*dist x q

noncomputable def metricConeApprox (φ : Y → ℝ) (K : ℝ≥0) : ℕ → Y → ℝ
  | 0 => metricCone φ K (denseSeq Y 0)
  | n+1 => fun x => min (metricConeApprox φ K n x) (metricCone φ K (denseSeq Y (n+1)) x)

variable {X : Type*} [MetricSpace X]

structure LipLattice (P : (X → ℝ) → Prop) : Prop where
  const : ∀ c : ℝ, P (fun _ => c)
  linear : ∀ {u v : X → ℝ}, (∃ K, LipschitzWith K u) → (∃ K, LipschitzWith K v) →
    P u → P v → ∀ a c : ℝ, P (fun x => a*u x+c*v x)
  min : ∀ {u v : X → ℝ}, (∃ K, LipschitzWith K u) → (∃ K, LipschitzWith K v) →
    P u → P v → P (fun x => min (u x) (v x))
  max : ∀ {u v : X → ℝ}, (∃ K, LipschitzWith K u) → (∃ K, LipschitzWith K v) →
    P u → P v → P (fun x => max (u x) (v x))
  limit : ∀ {us : ℕ → X → ℝ} {u : X → ℝ} {K : ℝ≥0}, (∀ n, P (us n)) →
    (∀ n, LipschitzWith K (us n)) →
    (∀ x, Tendsto (fun n => us n x) atTop (𝓝 (u x))) → P u

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

noncomputable def shrinkingBump (j : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (j + 1 : ℝ)
  rOut := 2 / (j + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_JointPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV

noncomputable def shrinkingBump {E : Type*} [NormedAddCommGroup E] (j : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((j:ℝ)+1)
  rOut := 2 * (1 / ((j:ℝ)+1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1/((j:ℝ)+1) := by positivity
    linarith

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

noncomputable def betaRadius (r : ℝ) := r^2/(1+r^2)

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

noncomputable def sobolevP (n : ℕ) : ℝ := 2*n/(n-2)
noncomputable def sobolevQ (n : ℕ) : ℝ := 2*(n-1)/(n-2)
noncomputable def bubble (n : ℕ) (r : ℝ) : ℝ := (1+r^2)^(-((n:ℝ)-2)/2)
noncomputable def bubbleMass (n : ℕ) : ℝ :=
  Real.Gamma ((n:ℝ)/2)^2/(2*Real.Gamma n)

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Postcompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {k : ℕ}
  (C : IntegerChart X k) {f : X → Y} {K J : ℝ≥0}
noncomputable def postcompose (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) : IntegerChart Y k where
  domain := C.domain
  borel := C.borel
  bounded := C.bounded
  param := f ∘ C.param
  bilipschitz := by
    obtain ⟨L,U,hL,_⟩ := C.bilipschitz
    exact ⟨K*L,J,hf.comp hL,hJ⟩
  multiplicity := C.multiplicity
  integrable := C.integrable

end IntegerChart

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CycleDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
noncomputable def mixedTuple {ι : Type*} [LinearOrder ι] {E : ι → Type*}
    (a b : ∀ i, E i) (i : ι) : ∀ j, E j := fun j => if j < i then a j else b j

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_ClosedCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory
open scoped NNReal ENNReal Topology

abbrev ClosedCylinder (X : Type*) := Icc (0:ℝ) 1 × X
noncomputable def cylinderClamp {X : Type*} (p : ℝ × X) : ClosedCylinder X :=
  (projIcc 0 1 (by norm_num) p.1,p.2)
def cylinderEmbed {X : Type*} (p : ClosedCylinder X) : ℝ × X := (p.1.val,p.2)

lemma cylinderClamp_lipschitz {X : Type*} [MetricSpace X] :
    LipschitzWith 1 (cylinderClamp (X := X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq,cylinderClamp]
  refine max_le ?_ (le_max_right _ _)
  apply le_trans _ (le_max_left _ _)
  simpa only [NNReal.coe_one,one_mul] using
    (LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1)).dist_le_mul p.1 q.1

lemma cylinderEmbed_isometry {X : Type*} [MetricSpace X] :
    Isometry (cylinderEmbed (X := X)) := by
  exact (isometry_subtype_coe).prodMap isometry_id

lemma cylinderEmbed_clamp {X : Type*} (p : ℝ × X) (hp : p.1 ∈ Icc (0:ℝ) 1) :
    cylinderEmbed (cylinderClamp p) = p := by
  dsimp [cylinderEmbed,cylinderClamp]
  rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) hp]

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_SpatialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spatialRadialForm (g r t : ℝ) (α γ : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (1-t*g)^2 * (if i=j then 1 else 0) -
    (1-t*g)*t*r*(α i*γ j+γ i*α j) + t^2*r^2*γ i*γ j

end CAT0Fillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MetricDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def metricSpatialRadialForm (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) : Matrix ι ι ℝ :=
  (1-t*g)^2 • G-((1-t*g)*t*r) • (vecMulVec α γ+vecMulVec γ α)+
    (t^2*r^2) • vecMulVec γ γ

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_UniformSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Metric Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev RadialParameters (ι : Type*) := (ℝ × ℝ) × ((ι → ℝ) × (ι → ℝ))

def spatialRadialSlope (t : ℝ) (p : RadialParameters ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (-2*p.1.1+t*p.1.1^2)*(if i=j then 1 else 0)-
    (1-t*p.1.1)*p.1.2*(p.2.1 i*p.2.2 j+p.2.2 i*p.2.1 j)+
    t*p.1.2^2*p.2.2 i*p.2.2 j

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TotalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def totalRankOneForm (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 H+
    vecMulVec (Sum.elim (fun _ => c) u) (Sum.elim (fun _ => c) u)

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TotalDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def metricTotalRadialForm (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  totalRankOneForm ((1-t*g)^2 • (G-vecMulVec α α)) (-r*g)
    ((1-t*g) • α-(t*r) • γ)

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_RadialChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace Prism

def zeroSumEquiv (k : ℕ) : Fin (k+1) ≃ Unit ⊕ Fin k where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := Fin.cases rfl (fun _ => rfl) i
  right_inv i := by rcases i with ⟨⟩ | i <;> rfl
end Prism

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_AtomGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def atomicTent (p : X) (r : ℝ) (z : X) : ℝ :=
  min (dist z p) (max 0 (r - dist z p))

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma atomicTent_center (p : X) (r : ℝ) : atomicTent p r p = 0 := by
  simp [atomicTent]

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev AtomCode := Σ m : ℕ, (Fin m → ℤ) × (Fin m → ℕ) × ℚ
namespace AtomCode
abbrev size (c : AtomCode) := c.1
abbrev weights (c : AtomCode) : Fin c.size → ℤ := c.2.1
abbrev centers (c : AtomCode) : Fin c.size → ℕ := c.2.2.1
abbrev radius (c : AtomCode) : ℝ := (c.2.2.2 : ℝ)

def Valid [SeparableSpace X] [Nonempty X] (c : AtomCode) : Prop :=
  0 < c.radius ∧ 4 * c.radius ≤ 1 ∧ (∀ i, c.weights i ≠ 0) ∧
    ∀ i j, i ≠ j → 8 * c.radius ≤
      dist (TopologicalSpace.denseSeq X (c.centers i)) (TopologicalSpace.denseSeq X (c.centers j))
end AtomCode

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_LipschitzPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

def DensityPiece (ν : Measure E) (N j : ℕ) : Set E :=
  {x | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 / (j+1 : ℝ) →
    ν.real (closedBall x q) ≤ (N : ℝ) * μ.real (closedBall x q)}

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_BorelAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

abbrev JointPieceIndex := ℕ × ℕ × ℕ × ℕ

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_GraphCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

abbrev FullGraphIndex := JointPieceIndex × AtomCode

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_ScalarCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings

noncomputable def reindexFactor {k : ℕ} (ρ : Fin k → Fin k) : ℝ :=
  (Matrix.of fun i j => if ρ i = j then (1:ℝ) else 0).det

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_JointCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

abbrev FullGraphCode := Σ (_ : ℕ × ℕ) (i : FullGraphIndex), Fin i.2.size

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma memLp_smul_bounded {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) :
    MemLp (fun x => b x • g x) 2 μ := by
  apply (Lp.memLp g).of_le_mul (c := C) (hb.smul (Lp.aestronglyMeasurable g))
  filter_upwards [hC] with x hx
  change ‖b x • g x‖ ≤ C*‖g x‖
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

noncomputable def mulLp {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) : Lp E 2 μ :=
  (memLp_smul_bounded hb hC g).toLp _

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

local instance instMeasurableSpaceMatrixFinReal_solutions_2 {n : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def levelApprox (a ε t : ℝ) := ε*Real.arctan ((t-a)/ε)
noncomputable def levelApproxDeriv (a ε t : ℝ) := ε^2/(ε^2+(t-a)^2)

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_AbsoluteValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def absApprox (ε t : ℝ) : ℝ := Real.sqrt (t^2+ε^2)
noncomputable def absApproxDeriv (ε t : ℝ) : ℝ := t / Real.sqrt (t^2+ε^2)

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
noncomputable def binaryDerivative (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ
end CAT0Fillings.ClosedCalculus

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Piecewise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def scalarAverage (F : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  ((∫ z in (0:ℝ)..(t+ε), F z)-(∫ z in (0:ℝ)..(t-ε), F z))/(2*ε)
noncomputable def scalarAverageDeriv (F : ℝ → ℝ) (ε t : ℝ) : ℝ :=
  (F (t+ε)-F (t-ε))/(2*ε)

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_Truncated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def truncatedPower (γ N t : ℝ) : ℝ :=
  max t 0 * (min (max t 0) N)^(γ-1)

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
noncomputable def truncatedPowerSlope (γ N t : ℝ) : ℝ :=
  if t < N then γ*t^(γ-1) else N^(γ-1)

end CAT0Fillings.ClosedCalculus

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.ClosedCalculus
noncomputable def lowerCut (j : ℕ) : ℝ := 1/((j:ℝ)+2)
noncomputable def upperCut (j : ℕ) : ℝ := (j:ℝ)+2
end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Conformal_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter
open scoped Topology

namespace CAT0Fillings.Conformal
noncomputable def profile (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1^m*z.2^α*f (κ*z.1*z.2^β)

end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Conformal_Closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
noncomputable def profileRD (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (r z : ℝ) : ℝ :=
  (m:ℝ)*r^(m-1)*z^α*f (κ*r*z^β)+κ*r^m*z^(α+β)*deriv f (κ*r*z^β)
noncomputable def profileZD (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (r z : ℝ) : ℝ :=
  α*r^m*z^(α-1)*f (κ*r*z^β)+β*κ*r^(m+1)*z^(α+β-1)*deriv f (κ*r*z^β)
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MetricSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix Set Metric
open scoped BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev MetricRadialParameters (ι : Type*) := Matrix ι ι ℝ × RadialParameters ι

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_IntegralDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
local instance instMeasurableSpaceMatrixReal_solutions_1 : MeasurableSpace (Matrix ι ι ℝ) := borel _

end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

local instance instMeasurableSpaceMatrixReal_solutions_2 : MeasurableSpace (Matrix ι ι ℝ) := borel _

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_NormalizedDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ} (C : IntegerChart X k)
local instance instMeasurableSpaceMatrixFinReal_1 : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := _root_.borel _
end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ClosedInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*}
  [MetricSpace X]
  [MeasurableSpace X]
  [BorelSpace X]
  [CompactSpace X]
  [Nonempty X]
  {k : ℕ}
  {T : Functional X (k+1)}
  {hT : IsMetricCurrent T}

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma radius_bound [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (o x : X) : dist o x ≤ Metric.diam (univ : Set X) :=
  Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_TestIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
noncomputable def profileGradient {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (r u : ℝ) (R V : E) : E :=
  if 0 < u then profileRD m α β κ f r u • R+profileZD m α β κ f r u • V else 0
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_AverageProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
noncomputable def averageProfile (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Icc (0:ℝ) 1, τ^(n-1)*(d (τ*t))^2
noncomputable def averageProfileDeriv (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Icc (0:ℝ) 1, 2*τ^n*d (τ*t)*deriv d (τ*t)
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Fubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings

namespace ChordTransform

open MeasureTheory

noncomputable def kernel (n b a : ℝ) : ℝ := (1 + a*b) ^ (-n)

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def transform (n : ℝ) (b : α → ℝ) (a : ℝ) : ℝ :=
  ∫ x, kernel n (b x) a ∂μ

end ChordTransform

end CAT0Fillings

namespace CAT0Fillings.ChordAverage

noncomputable def average (q : ℝ) (J : ℝ → ℝ) (a : ℝ) : ℝ :=
  q * ∫ u in (0 : ℝ)..1, J (a*u) * u^(q-1)

end CAT0Fillings.ChordAverage

open Set Filter MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Blowup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity

noncomputable def boundedCoordinate (u : ℝ) (N : ℝ) : ℝ := min (max u 0) N
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X]

noncomputable def chartExtension {s : Set E} (φ : s → X) (z : s) (x : E) : X := by
  classical
  exact if hx : x ∈ s then φ ⟨x,hx⟩ else φ z

end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_CurrentDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
def HasTangentBound (μ : Measure X) (U : X → ℝ) (n : ℕ) (β : ℝ) (y : X) : Prop :=
  ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
    ∀ (B : ℕ → ℝ≥0∞) (L : ℝ≥0∞),
    (∀ j, ENNReal.ofReal ((ε j^n)⁻¹) *
      ∫⁻ x, ENNReal.ofReal (U x^(2*(n:ℝ)*β)/
        (1+(U y^β)^2*(dist x y/ε j)^2*U x^(2*β))^n) ∂μ ≤ B j) →
    Tendsto B atTop (𝓝 L) → ENNReal.ofReal (sphereArea n/(2:ℝ)^n) ≤ L
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Barycenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def squaredPotential (μ : Measure X) (y : X) : ℝ := ∫ x, dist y x ^ 2 ∂μ

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Bubble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
noncomputable def chordBubble (q a t : ℝ) : ℝ := (1+a*t^2)^(-q)
noncomputable def chordBubbleD (q a t : ℝ) : ℝ := -2*q*a*t*(1+a*t^2)^(-q-1)
noncomputable def chordBubbleDD (q a t : ℝ) : ℝ :=
  -2*q*a*(1+a*t^2)^(-q-1)+4*q*(q+1)*a^2*t^2*(1+a*t^2)^(-q-2)
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing JointBV

variable {X : Type*}
  [MetricSpace X]
  [MeasurableSpace X]
  [BorelSpace X]
  [CompactSpace X]
  [Nonempty X]
  {k : ℕ}
  {T : Functional X (k+1)}
  {hT : IsMetricCurrent T}

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma mul_bounded {b u : X → ℝ} {B U : ℝ≥0}
    (hb : ∀ x, |b x| ≤ B) (hu : ∀ x, |u x| ≤ U) (x : X) : |b x*u x| ≤ (B*U:ℝ≥0) := by
  rw [abs_mul]
  exact mul_le_mul (hb x) (hu x) (abs_nonneg _) B.coe_nonneg

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Tails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.JointBV
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (ρ : α → ℕ) (hρ : Measurable ρ)

def indexTail (N : ℕ) (x : α) : ℝ := if N ≤ ρ x then 1 else 0

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_InverseCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

noncomputable def inverseSquareCutoff (ε r : ℝ) : ℝ := ε^2/(max ε r)^2

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_RadialEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

noncomputable def cutoffVariationWeight (ε r a : ℝ) : ℝ :=
  if r < ε then 2 else 2*inverseSquareCutoff ε r*(1-a)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_RadialCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.RadialSobolev

noncomputable def cumulativeOrderIso {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) :
    Icc a b ≃o Icc (F a) (F b) := by
  let f : Icc a b → Icc (F a) (F b) := fun x =>
    ⟨F x,⟨hm.monotoneOn ⟨le_rfl,hab⟩ x.property x.property.1,
      hm.monotoneOn x.property ⟨hab,le_rfl⟩ x.property.2⟩⟩
  apply StrictMono.orderIsoOfSurjective f
  · intro x y hxy
    exact hm x.property y.property hxy
  · intro y
    obtain ⟨x,hx,he⟩ := intermediate_value_Icc hab hF y.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩

noncomputable def cumulativeInverse {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (y : ℝ) : ℝ :=
  ((cumulativeOrderIso hab hF hm).symm
    (projIcc (F a) (F b) (hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) y) : ℝ)

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.RadialSobolev

noncomputable def radialCDF (n : ℕ) (ω : ℝ) (f : ℝ → ℝ) (p r : ℝ) : ℝ :=
  (n:ℝ)*ω*∫ s in (0:ℝ)..r, s^(n-1)*(f s)^p

lemma radialCDF_hasDerivAt {n : ℕ} {ω p r : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hp : 0 < p) :
    HasDerivAt (radialCDF n ω f p)
      ((n:ℝ)*ω*r^(n-1)*(f r)^p) r := by
  have hc : Continuous (fun s : ℝ => s^(n-1)*(f s)^p) :=
    (continuous_id.pow _).mul (hf.rpow_const (fun _ => Or.inr hp.le))
  change HasDerivAt (fun y => (n:ℝ)*ω*∫ s in (0:ℝ)..y, s^(n-1)*(f s)^p) _ r
  simpa only [mul_assoc] using
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul ((n:ℝ)*ω)

lemma radialCDF_continuous {n : ℕ} {ω p : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hp : 0 < p) : Continuous (radialCDF n ω f p) :=
  continuous_iff_continuousAt.mpr fun _ => (radialCDF_hasDerivAt hf hp).continuousAt

lemma radialCDF_strictMonoOn {n : ℕ} {ω p R : ℝ} {f : ℝ → ℝ}
    (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hp : 0 < p)
    (hpos : ∀ r ∈ Ioo 0 R, 0 < f r) :
    StrictMonoOn (radialCDF n ω f p) (Icc 0 R) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (radialCDF_continuous hf hp).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(radialCDF_hasDerivAt hf hp).deriv]
    exact mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos hx.1 _))
      (Real.rpow_pos_of_pos (hpos x hx) _)

noncomputable def radialTransport {n : ℕ} {ω p D : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hg : Continuous g) (hp : 0 < p)
    (hgp : ∀ r ∈ Ioo 0 D, 0 < g r) (r : ℝ) : ℝ :=
  cumulativeInverse hD (radialCDF_continuous hg hp).continuousOn
    (radialCDF_strictMonoOn hn hω hg hp hgp) (radialCDF n ω f p r)

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

noncomputable def radialInverse (R : ℝ → ℝ) (U ρ : ℝ) : ℝ :=
  sSup {t | 0 ≤ t ∧ t < U ∧ ρ < R t}

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Scaling_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings

def ScaledSpace (X : Type*) (_c : ℝ≥0) := X
namespace ScaledSpace
variable {X : Type*} [m : MetricSpace X] (c : ℝ≥0) [NeZero c]
instance instTopologicalSpace : TopologicalSpace (ScaledSpace X c) := inferInstanceAs (TopologicalSpace X)
instance instMeasurableSpace [MeasurableSpace X] : MeasurableSpace (ScaledSpace X c) := inferInstanceAs (MeasurableSpace X)
def toBase (x : ScaledSpace X c) : X := x
def ofBase (x : X) : ScaledSpace X c := x
noncomputable instance instMetricSpace : MetricSpace (ScaledSpace X c) :=
  MetricSpace.ofDistTopology
    (fun x y : ScaledSpace X c => (c:ℝ)*dist (toBase c x) (toBase c y))
    (by intro x; simp)
    (by intro x y; rw [dist_comm])
    (by intro x y z; simpa only [mul_add] using mul_le_mul_of_nonneg_left (dist_triangle (toBase c x) (toBase c y) (toBase c z)) c.coe_nonneg)
    (by
      have hc : 0 < (c:ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (NeZero.ne c))
      intro s
      change @IsOpen X inferInstance (fun x => ofBase c x ∈ s) ↔ _
      have ho := @Metric.isOpen_iff X m.toPseudoMetricSpace (fun x => ofBase c x ∈ s)
      apply ho.trans
      constructor
      · intro hs x hx
        obtain ⟨e,he,hb⟩ := hs (toBase c x) hx
        refine ⟨c*e,mul_pos hc he,fun y hy => hb (a := toBase c y) ?_⟩
        rw [mem_ball,dist_comm]
        exact (mul_lt_mul_iff_right₀ hc).mp hy
      · intro hs x hx
        obtain ⟨e,he,hb⟩ := hs (ofBase c x) hx
        refine ⟨e/c,div_pos he hc,fun y hy => hb (ofBase c y) ?_⟩
        change (c:ℝ)*dist x y < e
        rw [mem_ball,dist_comm] at hy
        simpa only [mul_comm] using (lt_div_iff₀ hc).mp hy)
    (by
      intro x y h
      have he := dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (NNReal.coe_ne_zero.mpr (NeZero.ne c)))
      exact congrArg (ofBase c) he)
instance instCompactSpace [CompactSpace X] : CompactSpace (ScaledSpace X c) := inferInstanceAs (CompactSpace X)
instance instNonempty [Nonempty X] : Nonempty (ScaledSpace X c) := inferInstanceAs (Nonempty X)
instance instBorelSpace [MeasurableSpace X] [BorelSpace X] : BorelSpace (ScaledSpace X c) := inferInstanceAs (BorelSpace X)
end ScaledSpace
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
universe u
noncomputable def cutoffRatio (R r : ℝ) : ℝ := if r ≤ R then 1 else R / r

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

noncomputable def negativeTail (μ : Measure ℝ) [IsFiniteMeasure μ] : StieltjesFunction ℝ where
  toFun t := -μ.real (Ioi t)
  mono' := fun a b hab => neg_le_neg (measureReal_mono (Ioi_subset_Ioi hab))
  right_continuous' t := by
    have h := (integrable_const (μ := μ) (1:ℝ)).integrableOn.continuousWithinAt_Ici_primitive_Ioi
      (a₀ := t)
    have h' : ContinuousWithinAt (fun b => μ.real (Ioi b)) (Ici t) t := by
      simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using h
    exact h'.neg

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

noncomputable def radiusDistribution (μ : Measure ℝ) (ω : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (μ.real (Ioi t)/ω) ^ (1/(n:ℝ))

variable (μ : Measure ℝ) {ω : ℝ} {n : ℕ}

variable [IsFiniteMeasure μ]

lemma radius_antitone (hω : 0 ≤ ω) : Antitone (radiusDistribution μ ω n) := by
  intro a b hab
  apply Real.rpow_le_rpow (div_nonneg measureReal_nonneg hω)
  · exact div_le_div_of_nonneg_right (measureReal_mono (Ioi_subset_Ioi hab)) hω
  · positivity

lemma radius_right_continuous (hω : 0 < ω) (hn : 0 < n) (t : ℝ) :
    ContinuousWithinAt (radiusDistribution μ ω n) (Ici t) t := by
  have htail : ContinuousWithinAt (fun s => μ.real (Ioi s)) (Ici t) t := by
    have hh := (negativeTail μ).right_continuous' t
    have hh' := hh.neg
    change ContinuousWithinAt (fun s => - -μ.real (Ioi s)) (Ici t) t at hh'
    simpa only [neg_neg] using hh'
  exact (htail.div continuousWithinAt_const hω.ne').rpow_const (Or.inr (by positivity))

noncomputable def negativeRadius (hω : 0 < ω) (hn : 0 < n) : StieltjesFunction ℝ where
  toFun t := -radiusDistribution μ ω n t
  mono' := (radius_antitone μ hω.le).neg
  right_continuous' t := (radius_right_continuous μ hω hn t).neg

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Euclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (ν : Measure E) [ν.IsAddHaarMeasure]

noncomputable def euclideanRearrangement (μ : Measure ℝ) (U : ℝ) (x : E) : ℝ :=
  radialInverse (radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E)) U ‖x‖

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

noncomputable def positiveTrunc (τ t : ℝ) : ℝ := max (|t|-τ) 0

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings

variable {X : Type*} [MetricSpace X]
noncomputable def ballCutoff (o : X) (R : ℝ) (x : X) : ℝ := min 1 (max 0 (R+1-dist x o))
end CAT0Fillings
end

end OAI
end


