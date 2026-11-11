-- Prove2me | Definitions.Def_OAIQ219IF000
-- name    : OAIQ219IF000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T13:32:32.185496+00:00
-- url     : https://prove2.me/theorems/0cd06eb2-cb3a-42fc-97f1-a79212458686
-- title:
--   Definitions bundle OAIQ219IF000 of the split of OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpIntegralFillings.coefficient_optimal`, carved from OpenAI's openai/math development (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 329 declarations of OpenAI's Lean: 83 definitions, 12 instances and 234 theorems. The definitions and types are `OAI.SharpIntegralFillings.BorelCoefficients.borelAction`, `OAI.SharpIntegralFillings.BorelCoefficients.coefficientLinear`, `OAI.SharpIntegralFillings.BorelCoefficients.l1Action`, `OAI.SharpIntegralFillings.BorelCoefficients.lipAlgebra`, `OAI.SharpIntegralFillings.BorelCoefficients.lipToL1`, `OAI.SharpIntegralFillings.BorelCoefficients.weightedCurrent`, `OAI.SharpIntegralFillings.BorelRestriction.restrictCurrent`, `OAI.SharpIntegralFillings.BoundedLip.toBoundedContinuous`, `OAI.SharpIntegralFillings.CurrentOperations.pushCurrent`, `OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap`, `OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap`, `OAI.SharpIntegralFillings.EuclideanStraightening.switchZero`, `OAI.SharpIntegralFillings.Foundations.TestClass`, `OAI.SharpIntegralFillings.Foundations.TestClass.eval`, `OAI.SharpIntegralFillings.Foundations.UnitTestClass`, `OAI.SharpIntegralFillings.HasTwoPointMetricDifferential`, `OAI.SharpIntegralFillings.IntegerChart.coordinateDomain`, `OAI.SharpIntegralFillings.IntegerChart.coordinateEmptyChart`, `OAI.SharpIntegralFillings.IntegerChart.coordinateLayer`, `OAI.SharpIntegralFillings.IntegerChart.coordinateMinor`, `OAI.SharpIntegralFillings.IntegerChart.coordinateParam`, `OAI.SharpIntegralFillings.IntegerChart.coordinateSlice`, `OAI.SharpIntegralFillings.IntegerChart.coordinateSliceTotal`, `OAI.SharpIntegralFillings.IntegerChart.extendOn`, `OAI.SharpIntegralFillings.IntegerChart.inverseParam`, `OAI.SharpIntegralFillings.IntegerChart.majorantMeasure`, `OAI.SharpIntegralFillings.IntegerChart.negate`, `OAI.SharpIntegralFillings.IntegerChart.paramExtended`, `OAI.SharpIntegralFillings.IntegerChart.postcompose`, `OAI.SharpIntegralFillings.IntegerChart.reparam`, `OAI.SharpIntegralFillings.IntegerChart.restrictDomain`, `OAI.SharpIntegralFillings.IntegerChart.restrictImage`, `OAI.SharpIntegralFillings.IntegerChart.restrictMultiplicity`, `OAI.SharpIntegralFillings.IntegerChart.sumMultiplicities`, `OAI.SharpIntegralFillings.IntegerChart.transition`, `OAI.SharpIntegralFillings.IntegerChart.withMultiplicity`, `OAI.SharpIntegralFillings.IsCAT0`, `OAI.SharpIntegralFillings.IsMetricCurrent.multilinear`, `OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure`, `OAI.SharpIntegralFillings.MassMeasure.weighted` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IntegralFillings_Charts_ChangeVariables`, `IntegralFillings_Charts_ContainingCharts`, `IntegralFillings_Charts_CurrentAxioms`, `IntegralFillings_Charts_CurrentContinuity`, `IntegralFillings_Charts_DensityPush`, `IntegralFillings_Charts_Differentiability`, `IntegralFillings_Charts_DomainRestriction`, `IntegralFillings_Charts_Extensions`, `IntegralFillings_Charts_ExtensionsLimit`, `IntegralFillings_Charts_ImageRestriction`, `IntegralFillings_Charts_IntegerSeries`, `IntegralFillings_Charts_Jacobian`, `IntegralFillings_Charts_LinearMass`, `IntegralFillings_Charts_MultiplicityRestriction`, `IntegralFillings_Charts_Orientation`, `IntegralFillings_Charts_OverlapSum`, `IntegralFillings_Charts_Postcompose`, `IntegralFillings_Charts_Reparametrization`, `IntegralFillings_Charts_Scalar`, `IntegralFillings_Charts_Straightening`, `IntegralFillings_Charts_Transitions`, `IntegralFillings_Currents_Basic`, `IntegralFillings_Currents_BorelAction`, `IntegralFillings_Currents_CanonicalMass`, `IntegralFillings_Currents_DenseTests`, `IntegralFillings_Currents_MassBounds`, `IntegralFillings_Currents_MassTests`, `IntegralFillings_Currents_Multilinear`, `IntegralFillings_Currents_Negation`, `IntegralFillings_Currents_Pushforward`, `IntegralFillings_Currents_Restriction`, `IntegralFillings_Currents_Summation`, `IntegralFillings_Currents_WeakCompactness`, `IntegralFillings_Currents_WeakMass`, `IntegralFillings_Currents_WeightedAction`, `IntegralFillings_Differentiation_Centered`, `IntegralFillings_Differentiation_CurveSpeed`, `IntegralFillings_Differentiation_Directional`, `IntegralFillings_Differentiation_ErrorModulus`, `IntegralFillings_Differentiation_HilbertCharts`, `IntegralFillings_Differentiation_ScalarBound`, `IntegralFillings_Differentiation_Seminorm`, `IntegralFillings_Differentiation_TwoPoint`, `IntegralFillings_Geometry_Comparison`, `IntegralFillings_Geometry_MatrixRows`, `IntegralFillings_Geometry_Polarization`, `IntegralFillings_Jacobian_ClosedForms`, `IntegralFillings_Jacobian_Coordinates`, `IntegralFillings_Jacobian_HeadEstimates`, `IntegralFillings_Jacobian_Lipschitz`, `IntegralFillings_Jacobian_Mixed`, `IntegralFillings_Jacobian_Smoothing`, `IntegralFillings_Jacobian_WeakLimits`, `IntegralFillings_Optimality_BallBoundary`, `IntegralFillings_Optimality_BallCoarea`, `IntegralFillings_Optimality_BallCurrent`, `IntegralFillings_Optimality_BallStokes`, `IntegralFillings_Optimality_Calibration`, `IntegralFillings_Slicing_CoordinateChart`, `IntegralFillings_Slicing_CoordinateCoarea`, `IntegralFillings_Slicing_CoordinateDerivative`, `IntegralFillings_Slicing_CoordinateIntegral`, `IntegralFillings_Slicing_EuclideanSplit`, `IntegralFillings_Slicing_Profiles`.
--
--   **Imports.** It imports the published bundle `Def_FillingCoefficient`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea`, `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts` and `OAI.SharpIntegralFillings.IntegerChart.hilbert_mass_measure_le`; the proofs of `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea`, `OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts`, `OAI.SharpIntegralFillings.IntegerChart.hilbert_mass_measure_le` and `OAI.SharpIntegralFillings.coefficient_optimal`.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_FillingCoefficient

section
-- module Solutions.OAIQ219_IF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h

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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_DensityPush
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open MeasureTheory

noncomputable def densityPush {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) (ρ : α → ℝ) : Measure β := by
  classical
  exact if AEMeasurable φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) then
    Measure.map φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) else 0

lemma densityPush_eq_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ) :
    densityPush μ φ ρ = Measure.map φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  exact ite_eq_left hφ.aemeasurable

lemma densityPush_finite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) {ρ : α → ℝ} (hρ : Integrable ρ μ) :
    IsFiniteMeasure (densityPush μ φ ρ) := by
  let := isFiniteMeasure_withDensity_ofReal hρ.hasFiniteIntegral
  unfold densityPush
  split
  · exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  · infer_instance

lemma integral_densityPush {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {ρ : α → ℝ}
    (hρ : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    {b : β → ℝ} (hb : Continuous b) :
    (∫ x, b x ∂densityPush μ φ ρ) = ∫ z, ρ z*b (φ z) ∂μ := by
  rw [densityPush_eq_map μ hφ,integral_map hφ.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings

attribute [local instance] Classical.propDecidable

universe u

section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

namespace BoundedLip
omit [MeasurableSpace X] in
lemma continuous {b : X → ℝ} (hb : BoundedLip b) : Continuous b :=
  hb.1.choose_spec.continuous

omit [MeasurableSpace X] in
lemma const (a : ℝ) : BoundedLip (fun _ : X => a) := by
  exact ⟨⟨0, LipschitzWith.const a⟩, |a|, fun _ => le_rfl⟩

omit [MeasurableSpace X] in
lemma add {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c) :
    BoundedLip (fun x => b x + c x) := by
  obtain ⟨⟨Kb, hKb⟩, Mb, hMb⟩ := hb
  obtain ⟨⟨Kc, hKc⟩, Mc, hMc⟩ := hc
  refine ⟨⟨Kb + Kc, hKb.add hKc⟩, Mb + Mc, ?_⟩
  intro x
  exact (abs_add_le _ _).trans (add_le_add (hMb x) (hMc x))

omit [MeasurableSpace X] in
lemma const_mul (a : ℝ) {b : X → ℝ} (hb : BoundedLip b) :
    BoundedLip (fun x => a * b x) := by
  obtain ⟨⟨K, hK⟩, M, hM⟩ := hb
  refine ⟨⟨⟨|a|, abs_nonneg a⟩ * K, ?_⟩, |a| * M, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    change dist (a * b x) (a * b y) ≤ (|a| * (K : ℝ)) * dist x y
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    calc |a| * |b x - b y| ≤ |a| * ((K : ℝ) * dist x y) :=
           mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (abs_nonneg a)
         _ = _ := by ring
  · intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)
end BoundedLip

lemma isMetricCurrent_zero (k : ℕ) : IsMetricCurrent (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) where
  offDomain := by intros; rfl
  linearFirst := by intros; simp
  linearCoord := by intros; simp
  sequentialContinuity := by intros; exact tendsto_const_nhds
  locality := by intros; rfl
  finiteMass := by
    refine ⟨0, inferInstance, ?_⟩
    intro b π hb hπ
    simp

lemma mass_le_measure {k : ℕ} {T : Functional X k} {μ : Measure X}
    (hμ : IsFiniteMeasure μ) (hT : Controls T μ) : mass T ≤ μ.real univ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨ν, _, _, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨μ, hμ, hT, rfl⟩

omit [MeasurableSpace X] in
@[simp] lemma boundarySucc_zero (k : ℕ) :
    boundarySucc (fun (_ : X → ℝ) (_ : Fin (k+1) → X → ℝ) => 0) = fun _ _ => 0 := by
  funext b π
  simp [boundarySucc]

omit [MeasurableSpace X] in
@[simp] lemma boundary_zero (k : ℕ) :
    boundary (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = fun _ _ => 0 := by
  cases k with
  | zero => rfl
  | succ k => exact boundarySucc_zero k

noncomputable def emptyChart (k : ℕ) : IntegerChart X k where
  domain := ∅
  borel := MeasurableSet.empty
  bounded := Bornology.isBounded_empty
  param := fun z => False.elim z.property
  bilipschitz := by
    refine ⟨0, 0, ?_, ?_⟩
    · apply lipschitzWith_iff_dist_le_mul.mpr
      intro a b
      exact False.elim a.property
    · intro a b
      exact False.elim a.property
  multiplicity := fun _ => 0
  integrable := by simp

omit [MeasurableSpace X] in
@[simp] lemma emptyChart_image (k : ℕ) : (emptyChart (X := X) k).image = ∅ := by
  ext x
  simp [IntegerChart.image, emptyChart]

omit [MeasurableSpace X] in
@[simp] lemma emptyChart_action (k : ℕ) :
    (emptyChart (X := X) k).action = fun _ _ => 0 := by
  funext b π
  simp [IntegerChart.action, emptyChart]

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Multilinear
attribute [-simp] _root_.OAI.SharpIntegralFillings.boundarySucc_zero _root_.OAI.SharpIntegralFillings.boundary_zero _root_.OAI.SharpIntegralFillings.emptyChart_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
omit [MeasurableSpace X] in
lemma lipschitz_mul_real {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a : ℝ) :
    LipschitzWith (⟨|a|, abs_nonneg a⟩ * K) (fun x => a * f x) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  change dist (a * f x) (a * f y) ≤ (|a| * (K : ℝ)) * dist x y
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  calc |a| * |f x - f y| ≤ |a| * ((K : ℝ) * dist x y) :=
         mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg a)
       _ = _ := by ring

def lipSubmodule : Submodule ℝ (X → ℝ) where
  carrier := {f | ∃ K : ℝ≥0, LipschitzWith K f}
  zero_mem' := ⟨0, LipschitzWith.const 0⟩
  add_mem' := by
    rintro f g ⟨K, hK⟩ ⟨L, hL⟩
    exact ⟨K + L, hK.add hL⟩
  smul_mem' := by
    intro a f hf
    obtain ⟨K, hK⟩ := hf
    exact ⟨_, lipschitz_mul_real hK a⟩

omit [MeasurableSpace X] in
lemma lip_coe_update {k : ℕ} (π : Fin k → lipSubmodule (X := X))
    (i : Fin k) (f : lipSubmodule (X := X)) :
    (fun j => ((Function.update π i f) j : X → ℝ)) =
      Function.update (fun j => (π j : X → ℝ)) i (f : X → ℝ) := by
  funext j
  by_cases h : j = i <;> simp [h]

noncomputable def IsMetricCurrent.multilinear {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (b : X → ℝ) (hb : BoundedLip b) :
    MultilinearMap ℝ (fun _ : Fin k => lipSubmodule (X := X)) ℝ :=
  MultilinearMap.mk' (fun π => T b (fun i => π i)) (by
    intro π i f g
    have h := hT.linearCoord b
      (fun j => ((Function.update π i f) j : X → ℝ)) i (g : X → ℝ) 1 1
      ⟨hb, fun j => ((Function.update π i f) j).property⟩ g.property
    simpa only [lip_coe_update, Function.update_self, one_mul,
      Function.update_idem, Submodule.coe_add, Pi.add_def] using h) (by
    intro π i a f
    have h := hT.linearCoord b
      (fun j => ((Function.update π i f) j : X → ℝ)) i (f : X → ℝ) a 0
      ⟨hb, fun j => ((Function.update π i f) j).property⟩ f.property
    simpa only [lip_coe_update, Function.update_self, zero_mul, add_zero,
      Function.update_idem, Submodule.coe_smul, Pi.smul_def, smul_eq_mul] using h)

lemma IsMetricCurrent.scale_coordinates {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} (hb : BoundedLip b)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (a : Fin k → ℝ) :
    T b (fun i x => a i * π i x) = (∏ i, a i) * T b π := by
  let p : Fin k → lipSubmodule (X := X) := fun i => ⟨π i, hπ i⟩
  exact (hT.multilinear b hb).map_smul_univ a p

lemma IsMetricCurrent.eq_zero_of_const_coord {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (i : Fin k) (c : ℝ) (hc : ∀ x, π i x = c) :
    T b π = 0 := by
  apply hT.locality b π h
  exact ⟨i, univ, c, isOpen_univ, subset_univ _, fun x _ => hc x⟩

lemma IsMetricCurrent.eq_zero_of_zero_lipschitz_coord {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (i : Fin k) (hi : LipschitzWith 0 (π i)) :
    T b π = 0 := by
  cases isEmpty_or_nonempty X with
  | inl hempty =>
    let := hempty
    exact hT.eq_zero_of_const_coord h i 0 (fun x => isEmptyElim x)
  | inr hnonempty =>
    obtain ⟨x₀⟩ := hnonempty
    apply hT.eq_zero_of_const_coord h i (π i x₀)
    intro x
    apply dist_le_zero.mp
    simpa using hi.dist_le_mul x x₀

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_MassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
lemma IsMetricCurrent.mass_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {μ : Measure X} (hμ : Controls T μ)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := by
  by_cases hzero : ∃ i, K i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hTi := hT.eq_zero_of_zero_lipschitz_coord ⟨hb, fun j => ⟨K j, hK j⟩⟩ i
      (hi ▸ hK i)
    rw [hTi, abs_zero]
    exact mul_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg)
      (integral_nonneg fun x => abs_nonneg (b x))
  · have hpos : ∀ i, 0 < K i := fun i => pos_iff_ne_zero.mpr (fun hi => hzero ⟨i, hi⟩)
    have hposR : ∀ i, (0 : ℝ) < K i := fun i => hpos i
    let π' : Fin k → X → ℝ := fun i x => (K i : ℝ)⁻¹ * π i x
    have hπ' : ∀ i, LipschitzWith 1 (π' i) := by
      intro i
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      change dist ((K i : ℝ)⁻¹ * π i x) ((K i : ℝ)⁻¹ * π i y) ≤ 1 * dist x y
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr (hposR i)), one_mul]
      calc (K i : ℝ)⁻¹ * |π i x - π i y| ≤
          (K i : ℝ)⁻¹ * ((K i : ℝ) * dist x y) :=
            mul_le_mul_of_nonneg_left ((hK i).dist_le_mul x y) (inv_nonneg.mpr (hposR i).le)
        _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hposR i)), one_mul]
    have heq : (fun i x => (K i : ℝ) * π' i x) = π := by
      funext i x
      dsimp [π']
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hposR i)), one_mul]
    have hscale := hT.scale_coordinates hb (fun i => ⟨1, hπ' i⟩) (fun i => (K i : ℝ))
    rw [heq] at hscale
    rw [hscale, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (hμ b π' hb hπ')
      (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)

open scoped BoundedContinuousFunction

omit [MeasurableSpace X] in
noncomputable def BoundedLip.toBoundedContinuous {b : X → ℝ} (hb : BoundedLip b) :
    X →ᵇ ℝ where
  toFun := b
  continuous_toFun := hb.continuous
  map_bounded' := by
    obtain ⟨M, hM⟩ := hb.2
    refine ⟨M + M, fun x y => ?_⟩
    calc dist (b x) (b y) ≤ dist (b x) 0 + dist 0 (b y) := dist_triangle _ _ _
         _ ≤ M + M := by simpa using add_le_add (hM x) (hM y)

variable [BorelSpace X]

lemma continuous_integral_abs_boundedLip {b : X → ℝ} (hb : BoundedLip b) :
    Continuous (fun μ : FiniteMeasure X => ∫ x, |b x| ∂(μ : Measure X)) := by
  let f : X →ᵇ ℝ :=
    { toFun := fun x => |b x|
      continuous_toFun := continuous_abs.comp hb.continuous
      map_bounded' := by
        obtain ⟨M, hM⟩ := hb.2
        refine ⟨M + M, fun x y => ?_⟩
        calc dist |b x| |b y| ≤ dist |b x| 0 + dist 0 |b y| := dist_triangle _ _ _
             _ ≤ M + M := by simpa using add_le_add (hM x) (hM y) }
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f

lemma isClosed_controls {k : ℕ} (T : Functional X k) :
    IsClosed {μ : FiniteMeasure X | Controls T (μ : Measure X)} := by
  simp only [Controls, ofPred_forall]
  apply isClosed_iInter
  intro b
  apply isClosed_iInter
  intro π
  apply isClosed_iInter
  intro hb
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (continuous_integral_abs_boundedLip hb)

lemma IsMetricCurrent.exists_controls_mass_eq [CompactSpace X] {k : ℕ}
    {T : Functional X k} (hT : IsMetricCurrent T) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ ∧ mass T = μ.real univ := by
  obtain ⟨μ₀, hμ₀, hTμ₀⟩ := hT.finiteMass
  let ν₀ : FiniteMeasure X := ⟨μ₀, hμ₀⟩
  let C : Set (FiniteMeasure X) := {ν | ν.mass ≤ ν₀.mass} ∩ {ν | Controls T (ν : Measure X)}
  have hC : IsCompact C :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X ν₀.mass).inter_right (isClosed_controls T)
  have hne : C.Nonempty := by
    refine ⟨ν₀, ?_⟩
    change ν₀.mass ≤ ν₀.mass ∧ Controls T (ν₀ : Measure X)
    exact ⟨le_rfl, hTμ₀⟩
  obtain ⟨ν, hν, hmin⟩ := hC.exists_isMinOn hne
    FiniteMeasure.continuous_mass.continuousOn
  change ν.mass ≤ ν₀.mass ∧ Controls T (ν : Measure X) at hν
  have hmin' (η : FiniteMeasure X) (hη : Controls T (η : Measure X)) : ν.mass ≤ η.mass := by
    by_cases hle : η.mass ≤ ν₀.mass
    · exact hmin ⟨hle, hη⟩
    · exact hν.1.trans (le_of_not_ge hle)
  refine ⟨ν, inferInstance, hν.2, le_antisymm (mass_le_measure inferInstance hν.2) ?_⟩
  apply le_csInf
  · exact ⟨μ₀.real univ, μ₀, hμ₀, hTμ₀, rfl⟩
  · rintro r ⟨η, hη, htη, rfl⟩
    exact hmin' ⟨η, hη⟩ htη

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedLip.mul {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c) :
    BoundedLip (fun x => b x * c x) := by
  obtain ⟨⟨Kb, hKb⟩, Mb, hMb⟩ := hb
  obtain ⟨⟨Kc, hKc⟩, Mc, hMc⟩ := hc
  let B : ℝ≥0 := ⟨max Mb 0, le_max_right _ _⟩
  let C : ℝ≥0 := ⟨max Mc 0, le_max_right _ _⟩
  have hB (x : X) : |b x| ≤ (B : ℝ) := (hMb x).trans (le_max_left _ _)
  have hC (x : X) : |c x| ≤ (C : ℝ) := (hMc x).trans (le_max_left _ _)
  refine ⟨⟨B * Kc + C * Kb, ?_⟩, (B : ℝ) * (C : ℝ), ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    rw [Real.dist_eq]
    calc |b x * c x - b y * c y| = |b x * (c x - c y) + (b x - b y) * c y| := by
            congr 1; ring
      _ ≤ |b x| * |c x - c y| + |b x - b y| * |c y| := by
            simpa only [abs_mul] using abs_add_le (b x * (c x - c y)) ((b x - b y) * c y)
      _ ≤ (B : ℝ) * ((Kc : ℝ) * dist x y) + ((Kb : ℝ) * dist x y) * (C : ℝ) := by
            apply add_le_add
            · exact mul_le_mul (hB x) (hKc.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg
            · exact mul_le_mul (hKb.dist_le_mul x y) (hC y) (abs_nonneg _)
                (mul_nonneg Kb.coe_nonneg dist_nonneg)
      _ = ((B * Kc + C * Kb : ℝ≥0) : ℝ) * dist x y := by push_cast <;> ring
  · intro x
    rw [abs_mul]
    exact mul_le_mul (hB x) (hC x) (abs_nonneg _) B.coe_nonneg

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_DenseTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u

lemma tendsto_of_lipschitz_dense {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {κ : Type*} {D : κ → A} (hD : DenseRange D)
    (hlim : ∀ i, Tendsto (fun j => f j (D i)) l (𝓝 (g (D i))))
    (x : A) : Tendsto (fun j => f j x) l (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨i, hi⟩ := hD.exists_dist_lt x hδ
  have hdr : (K : ℝ) * dist x (D i) < ε / 4 := by
    have hpos : 0 < (K : ℝ) + 1 := by positivity
    have hm := (mul_lt_mul_of_pos_left hi hpos)
    have heq : ((K : ℝ) + 1) * δ = ε / 4 := by
      dsimp [δ]
      field_simp
    rw [heq] at hm
    calc (K : ℝ) * dist x (D i) ≤ ((K : ℝ) + 1) * dist x (D i) := by
          nlinarith [dist_nonneg (x := x) (y := D i)]
      _ < _ := hm
  filter_upwards [(Metric.tendsto_nhds.mp (hlim i)) (ε / 2) (half_pos hε)] with j hj
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j (D i)) + dist (f j (D i)) (g (D i)) + dist (g (D i)) (g x) :=
        (dist_triangle _ (g (D i)) _).trans (add_le_add (dist_triangle _ (f j (D i)) _) le_rfl)
    _ < ε / 4 + ε / 2 + ε / 4 := by
      apply add_lt_add
      · exact add_lt_add ((hf j).dist_le_mul x (D i) |>.trans_lt hdr) hj
      · rw [dist_comm]
        exact (hg.dist_le_mul x (D i)).trans_lt hdr
    _ = ε := by ring

namespace BorelCoefficients

variable {X : Type u} [MetricSpace X] [CompactSpace X]

def lipAlgebra : Subalgebra ℝ C(X, ℝ) where
  carrier := {f | BoundedLip f}
  algebraMap_mem' r := BoundedLip.const r
  add_mem' hf hg := BoundedLip.add hf hg
  mul_mem' hf hg := BoundedLip.mul hf hg

lemma lipAlgebra_separates : (lipAlgebra (X := X)).SeparatesPoints := by
  intro x y hxy
  let f : C(X, ℝ) := ⟨fun z => dist z x, continuous_id.dist continuous_const⟩
  have hf : BoundedLip f := by
    refine ⟨⟨1, LipschitzWith.dist_left x⟩, ‖f‖, ?_⟩
    intro z
    exact (ContinuousMap.norm_coe_le_norm f z)
  refine ⟨f, ⟨f, hf, rfl⟩, ?_⟩
  change dist x x ≠ dist y x
  simpa only [dist_self, ne_eq, eq_comm, dist_eq_zero] using hxy.symm

lemma lipAlgebra_dense : DenseRange (fun f : lipAlgebra (X := X) => (f : C(X, ℝ))) := by
  rw [denseRange_iff_closure_range]
  rw [Subtype.range_coe_subtype]
  change closure (lipAlgebra (X := X) : Set C(X, ℝ)) = univ
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (lipAlgebra (X := X)) lipAlgebra_separates
  exact congrArg (fun A : Subalgebra ℝ C(X, ℝ) => (A : Set C(X, ℝ))) h

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def lipToL1 : lipAlgebra (X := X) →ₗ[ℝ] Lp ℝ 1 μ :=
  (ContinuousMap.toLp 1 μ ℝ).toLinearMap.comp (lipAlgebra (X := X)).val.toLinearMap

lemma lipToL1_dense : DenseRange (lipToL1 μ) := by
  apply (ContinuousMap.toLp_denseRange ℝ μ ℝ (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp
    lipAlgebra_dense (ContinuousMap.toLp 1 μ ℝ).continuous

lemma norm_lipToL1 (f : lipAlgebra (X := X)) :
    ‖lipToL1 μ f‖ = ∫ x, |f.val x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val] with x hx
  change ‖(ContinuousMap.toLp 1 μ ℝ f.val) x‖ = |f.val x|
  rw [hx, Real.norm_eq_abs]

end BorelCoefficients
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Differentiability
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

namespace SharpIntegralFillings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

lemma tangentConeAt_eq_univ_of_density_one (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) : tangentConeAt ℝ s x = univ := by
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z (ε / 2))).Nonempty :=
    Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, ⟨y, ys, hy⟩, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, ha, hya⟩ : ∃ a, a ∈ closedBall z (ε / 2) ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    exact ⟨a, ha, by simp only [h, add_neg_cancel_left]⟩
  refine ⟨a, ?_, ?_⟩
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hra : r • a ∈ U ∩ (x + ·) ⁻¹' s :=
      ⟨hrU (smul_mem_smul_set ha), by simpa only [mem_preimage, ← hya] using ys⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ hr0 a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using ha) (half_lt_self hε)

lemma uniqueDiffWithinAt_of_density_one (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) : UniqueDiffWithinAt ℝ s x := by
  have ht := tangentConeAt_eq_univ_of_density_one μ s x hx
  rw [uniqueDiffWithinAt_iff, ht]
  exact ⟨by simp, mem_closure_of_nonempty_tangentConeAt (by rw [ht]; exact univ_nonempty)⟩

lemma ae_uniqueDiffWithinAt (s : Set E) :
    ∀ᵐ x ∂μ.restrict s, UniqueDiffWithinAt ℝ s x := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s] with x hx
  exact uniqueDiffWithinAt_of_density_one μ s x hx

lemma ae_fderivWithin_eq_fderiv_extension {s : Set E} (hs : MeasurableSet s)
    {f F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (heq : EqOn f F s) :
    ∀ᵐ x ∂μ.restrict s, fderivWithin ℝ f s x = fderiv ℝ F x := by
  filter_upwards [ae_uniqueDiffWithinAt μ s, ae_restrict_mem hs,
    (hF.ae_differentiableAt (μ := μ)).filter_mono (ae_mono Measure.restrict_le_self)]
    with x hx hxs hFx
  rw [fderivWithin_congr' heq hxs, fderivWithin_eq_fderiv hx hFx]

lemma ae_norm_fderivWithin_le {s : Set E} (hs : MeasurableSet s)
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f s) :
    ∀ᵐ x ∂μ.restrict s, ‖fderivWithin ℝ f s x‖ ≤ L := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ hs hF heq] with x hx
  rw [hx]
  exact norm_fderiv_le_of_lipschitz ℝ hF

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ChangeVariables
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
lemma lipschitzOn_image_null {s : Set E} {f : E → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : μ s = 0) : μ (f '' s) = 0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have ha : H ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure H μ
  have hb : μ ≪ H := Measure.absolutelyContinuous_isAddHaarMeasure μ H
  apply hb
  apply le_antisymm _ zero_le
  have hi := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  change H (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * H s at hi
  simpa only [ha hs,mul_zero] using hi

lemma lipschitzOn_image_ae_congr_subset {s t : Set E} {f : E → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hts : t ⊆ s) (heq : s =ᵐ[μ] t) :
    f '' s =ᵐ[μ] f '' t := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : f '' s \ f '' t ⊆ f '' (s \ t) := by
      rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,fun h => hy ⟨x,h,rfl⟩⟩,rfl⟩
    exact measure_mono_null hsub
      (lipschitzOn_image_null μ (hf.mono sdiff_subset) (ae_eq_set.mp heq).1)
  · rw [sdiff_eq_empty.mpr (image_mono hts),measure_empty]

lemma exists_measurable_full_derivative_domain {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ t, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s ∧
      ∀ x ∈ t, HasFDerivWithinAt f (fderivWithin ℝ f s x) t x := by
  let d : Set E := {x | x ∈ s ∧ DifferentiableWithinAt ℝ f s x}
  have hd : d =ᵐ[μ] s := by
    filter_upwards [(ae_restrict_iff' hs).mp (hf.ae_differentiableWithinAt hs (μ := μ))] with x hx
    change (x ∈ s ∧ DifferentiableWithinAt ℝ f s x) = (x ∈ s)
    exact propext ⟨And.left,fun h => ⟨h,hx h⟩⟩
  obtain ⟨t,htd,htm,hteq⟩ := (hs.nullMeasurableSet.congr hd.symm).exists_measurable_subset_ae_eq
  have hts : t ⊆ s := fun x hx => (htd hx).1
  exact ⟨t,hts,htm,hteq.trans hd,fun x hx => (htd hx).2.hasFDerivWithinAt.mono hts⟩

lemma integrableOn_image_iff_integrableOn_abs_det_within {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) :
    IntegrableOn g (f '' s) μ ↔
      IntegrableOn (fun x => |(fderivWithin ℝ f s x).det| • g (f x)) s μ := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  exact (integrableOn_congr_set_ae (lipschitzOn_image_ae_congr_subset μ hf hts hteq.symm)).trans
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ htm htd (hinj.mono hts) g).trans
      (integrableOn_congr_set_ae hteq))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lipschitzOn_invFunOn {s : Set E} {f : E → E} {L : ℝ≥0}
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    LipschitzOnWith L (Function.invFunOn f s) (f '' s) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have h := ha _ (Function.invFunOn_mem hx) _ (Function.invFunOn_mem hy)
  simpa only [Function.invFunOn_eq hx,Function.invFunOn_eq hy] using h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma antilipschitzOn_injOn {s : Set E} {f : E → E} {L : ℝ≥0}
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    InjOn f s := by
  intro x hx y hy heq
  have h := ha x hx y hy
  rw [heq,dist_self,mul_zero] at h
  exact dist_le_zero.mp h

lemma aemeasurable_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    AEMeasurable (fderivWithin ℝ f s) (μ.restrict s) := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  have h := aemeasurable_fderivWithin μ htm htd
  rwa [Measure.restrict_congr_set hteq] at h

lemma ae_norm_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∀ᵐ x ∂μ.restrict s, ‖fderivWithin ℝ f s x‖ ≤ K := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  have hlin : ApproximatesLinearOn f (0 : E →L[ℝ] E) t K := by
    intro x hx y hy
    simpa only [_root_.zero_apply,sub_zero,←dist_eq_norm] using
      hf.dist_le_mul x (hts hx) y (hts hy)
  have h := hlin.norm_fderiv_sub_le μ htm (fderivWithin ℝ f s) htd
  rw [Measure.restrict_congr_set hteq] at h
  filter_upwards [h] with x hx
  exact_mod_cast (by simpa only [sub_zero] using hx : ‖fderivWithin ℝ f s x‖₊ ≤ K)

lemma ae_bound_det_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ C : ℝ, ∀ᵐ x ∂μ.restrict s, ‖(fderivWithin ℝ f s x).det‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) (K : ℝ)).exists_bound_of_continuousOn
    (ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := E)).continuousOn
  refine ⟨C,?_⟩
  filter_upwards [ae_norm_fderivWithin_lipschitzOn μ hs hf] with x hx
  exact hC _ (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma integrable_mul_det_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    {g : E → ℝ} (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x => g x * (fderivWithin ℝ f s x).det) s μ := by
  obtain ⟨C,hC⟩ := ae_bound_det_fderivWithin_lipschitzOn μ hs hf
  exact hg.mul_bdd ((ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
    (aemeasurable_fderivWithin_lipschitzOn μ hs hf)).aestronglyMeasurable) hC

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ExtensionsLimit
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

namespace SharpIntegralFillings
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
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
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

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Scalar
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

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma scalar_eq {f : X → ℝ} {z : Euc k} (hz : z ∈ C.domain) :
    C.scalar f z = f (C.param ⟨z, hz⟩) := by simp [scalar, hz]

lemma scalar_lipschitzOn {f : X → ℝ} {K L : ℝ≥0}
    (hφ : LipschitzWith L C.param) (hf : LipschitzWith K f) :
    LipschitzOnWith (K * L) (C.scalar f) C.domain := by
  apply lipschitzOnWith_iff_restrict.mpr
  convert hf.comp hφ using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact C.scalar_eq z.property

lemma measurable_scalar {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Measurable (C.scalar f) := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  obtain ⟨F, hF, heq⟩ := (C.scalar_lipschitzOn hφ hf).extend_real
  have hsc : C.scalar f = C.domain.indicator F := by
    funext z
    by_cases hz : z ∈ C.domain
    · simpa [hz] using heq hz
    · simp [scalar, hz]
  rw [hsc]
  exact hF.continuous.measurable.indicator C.borel

lemma ae_differentiableWithinAt_scalar {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ z ∂volume.restrict C.domain, DifferentiableWithinAt ℝ (C.scalar f) C.domain z := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  obtain ⟨F, hF, heq⟩ := (C.scalar_lipschitzOn hφ hf).extend_real
  filter_upwards [ae_restrict_mem C.borel,
    (hF.ae_differentiableAt (μ := volume)).filter_mono (ae_mono Measure.restrict_le_self)]
    with z hz hd
  exact hd.differentiableWithinAt.congr heq (heq hz)

lemma ae_jacobian_eq_extensions {π : Fin k → X → ℝ} {F : Fin k → Euc k → ℝ}
    {L : Fin k → ℝ≥0} (hF : ∀ i, LipschitzWith (L i) (F i))
    (heq : ∀ i, EqOn (C.scalar (π i)) (F i) C.domain) :
    C.jacobian π =ᵐ[volume.restrict C.domain]
      fun z => Matrix.det (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1)) := by
  have hae : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      fderivWithin ℝ (C.scalar (π i)) C.domain z = fderiv ℝ (F i) z :=
    ae_all_iff.mpr fun i => ae_fderivWithin_eq_fderiv_extension volume C.borel (hF i) (heq i)
  filter_upwards [hae] with z hz
  simp only [jacobian, hz]
  rfl

lemma jacobian_aestronglyMeasurable {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    AEStronglyMeasurable (C.jacobian π) (volume.restrict C.domain) := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  choose K hK using hπ
  choose F hF heq using fun i => (C.scalar_lipschitzOn hφ (hK i)).extend_real
  have hmeas : Measurable (fun z => Matrix.det
      (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1))) := by
    simp only [Matrix.det_apply']
    fun_prop
  exact hmeas.aestronglyMeasurable.congr (C.ae_jacobian_eq_extensions hF heq).symm

end IntegerChart
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_ClosedForms
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_Mixed
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings

open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_Smoothing
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

namespace SharpIntegralFillings.VectorSmoothing
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

end SharpIntegralFillings.VectorSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_Lipschitz
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings

open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace SharpIntegralFillings
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

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_Coordinates
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings

namespace SharpIntegralFillings
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

end SharpIntegralFillings

namespace SharpIntegralFillings
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

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_HeadEstimates
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings

namespace SharpIntegralFillings
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

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Jacobian_WeakLimits
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings

namespace SharpIntegralFillings
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

end SharpIntegralFillings

open Set Filter Metric
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_CurrentContinuity
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

namespace SharpIntegralFillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma integrable_weight {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
      (volume.restrict C.domain) := by
  obtain ⟨K,hK⟩ := hb.1
  obtain ⟨M,hM⟩ := hb.2
  apply C.integrable.mul_bdd (C.measurable_scalar hK).aestronglyMeasurable
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simpa [C.scalar_eq hz,Real.norm_eq_abs] using hM (C.param ⟨z,hz⟩)

lemma action_eq_extended_jacobian {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) {F : Fin k → Euc k → ℝ} {K : ℝ≥0}
    (hF : ∀ i, LipschitzWith K (F i))
    (heq : ∀ i, EqOn (C.scalar (π i)) (F i) C.domain) :
    C.action b π = ∫ z,
      C.domain.indicator (fun z => (C.multiplicity z : ℝ) * C.scalar b z) z *
        coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
  rw [action,ite_eq_left h]
  have H := C.ae_jacobian_eq_extensions hF heq
  have H' : C.jacobian π =ᵐ[volume.restrict C.domain]
      coordinateJacobian F (fun j => EuclideanSpace.single j 1) := by
    filter_upwards [H] with z hz
    rw [hz,coordinateJacobian,← Matrix.det_transpose]
    rfl
  calc
    _ = ∫ z in C.domain, ((C.multiplicity z : ℝ) * C.scalar b z) *
        coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
      apply integral_congr_ae
      filter_upwards [H'] with z hz
      rw [hz]
    _ = _ := by
      rw [← integral_indicator C.borel]
      apply integral_congr_ae
      filter_upwards [] with z
      exact Set.indicator_mul_left _ _ _

lemma action_sequentialContinuity (b : X → ℝ) (π : Fin k → X → ℝ)
    (πs : ℕ → Fin k → X → ℝ) (hb : BoundedLip b)
    (hπs : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hlim : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) :
    Tendsto (fun j => C.action b (πs j)) atTop (𝓝 (C.action b π)) := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  choose Ks hKs using hπs
  let K : ℝ≥0 := ∑ i, Ks i
  have hK (i : Fin k) : Ks i ≤ K :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  have hseq (j : ℕ) (i : Fin k) : LipschitzWith K (πs j i) := (hKs i j).weaken (hK i)
  have hπ (i : Fin k) : LipschitzWith K (π i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hlim i x).dist (hlim i y))
      (Eventually.of_forall fun j => (hseq j i).dist_le_mul x y)
  have htot : TotallyBounded C.domain := C.bounded.isCompact_closure.totallyBounded.subset subset_closure
  have hsc (i : Fin k) (j : ℕ) : LipschitzOnWith (K*L) (C.scalar (πs j i)) C.domain :=
    C.scalar_lipschitzOn hφ (hseq j i)
  have hlsc (i : Fin k) (z : Euc k) (hz : z ∈ C.domain) :
      Tendsto (fun j => C.scalar (πs j i) z) atTop (𝓝 (C.scalar (π i) z)) := by
    simpa only [C.scalar_eq hz] using hlim i (C.param ⟨z,hz⟩)
  choose Fs F hFs hF heqs heq hlimF using fun i =>
    exists_convergent_lipschitz_extensions htot (hsc i) (hlsc i)
  let a : Euc k → ℝ := C.domain.indicator (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
  have ha : Integrable a volume := (integrable_indicator_iff C.borel).mpr (C.integrable_weight hb)
  have H := weak_coordinateJacobian volume k (fun j i => hFs i j) hF hlimF
    (fun j => EuclideanSpace.single j 1) ha
  have heqs' (j : ℕ) := C.action_eq_extended_jacobian ⟨hb,fun i => ⟨K,hseq j i⟩⟩
    (fun i => hFs i j) (fun i => heqs i j)
  have heq' := C.action_eq_extended_jacobian ⟨hb,fun i => ⟨K,hπ i⟩⟩ hF heq
  simpa only [heqs',heq'] using H

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Jacobian
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

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma exists_jacobian_bound {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∃ B : ℝ, ∀ᵐ z ∂volume.restrict C.domain, ‖C.jacobian π z‖ ≤ B := by
  obtain ⟨L, U, hφ, _⟩ := C.bilipschitz
  choose K hK using hπ
  let R : ℝ := ∑ i, (K i * L : ℝ≥0)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact
    (Icc (fun (_ _ : Fin k) => -R) (fun _ _ => R))).exists_bound_of_continuousOn
      continuous_id.matrix_det.continuousOn
  refine ⟨B, ?_⟩
  have hae : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ ≤ (K i * L : ℝ≥0) :=
    ae_all_iff.mpr fun i => ae_norm_fderivWithin_le volume C.borel
      (C.scalar_lipschitzOn hφ (hK i))
  filter_upwards [hae] with z hz
  apply hB
  have hentry (i j : Fin k) :
      |(fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1)| ≤ R := by
    calc |(fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1)| ≤
        ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ := by
          simpa using (fderivWithin ℝ (C.scalar (π i)) C.domain z).le_opNorm
            (EuclideanSpace.single j 1)
      _ ≤ (K i * L : ℝ≥0) := hz i
      _ ≤ R := Finset.single_le_sum (fun i _ => NNReal.coe_nonneg (K i * L)) (Finset.mem_univ i)
  exact ⟨fun i j => (abs_le.mp (hentry i j)).1,
    fun i j => (abs_le.mp (hentry i j)).2⟩

lemma integrable_action_integrand {b : X → ℝ} {π : Fin k → X → ℝ}
    (hb : BoundedLip b) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z * C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨K, hK⟩ := hb.1
  obtain ⟨M, hM⟩ := hb.2
  have hbint : Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
      (volume.restrict C.domain) := by
    apply C.integrable.mul_bdd (C.measurable_scalar hK).aestronglyMeasurable
    filter_upwards [ae_restrict_mem C.borel] with z hz
    simpa [C.scalar_eq hz, Real.norm_eq_abs] using hM (C.param ⟨z, hz⟩)
  obtain ⟨B, hB⟩ := C.exists_jacobian_bound hπ
  exact hbint.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

lemma jacobian_update (π : Fin k → X → ℝ) (i : Fin k) (f : X → ℝ) (z : Euc k) :
    C.jacobian (Function.update π i f) z =
      (Matrix.updateRow
        (Matrix.of fun a j => fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1)) i
        (fun j => fderivWithin ℝ (C.scalar f) C.domain z (EuclideanSpace.single j 1))).det := by
  unfold jacobian
  congr 1
  funext a j
  by_cases ha : a = i
  · subst a
    simp
  · simp [ha]

end IntegerChart
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Extensions
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

namespace SharpIntegralFillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)
noncomputable def paramExtended : Euc k → X :=
  by classical exact fun z => if hz : z ∈ C.domain then C.param ⟨z,hz⟩ else Classical.arbitrary X

lemma measurable_paramExtended : Measurable C.paramExtended := by
  classical
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  exact hL.continuous.measurable.dite measurable_const C.borel

omit [MeasurableSpace X] [BorelSpace X] in
lemma scalar_ae_paramExtended (b : X → ℝ) :
    C.scalar b =ᵐ[volume.restrict C.domain] b ∘ C.paramExtended := by
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simp only [scalar,paramExtended,Function.comp_apply,dite_eq_left hz]

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_LinearMass
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

namespace SharpIntegralFillings
open MeasureTheory

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

noncomputable def majorantMeasure (J : Euc k → ℝ) : Measure X :=
  densityPush (volume.restrict C.domain) C.paramExtended
    (fun z => |(C.multiplicity z : ℝ)| * J z)

lemma majorant_controls {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian π z| ≤ J z) :
    Controls C.action (C.majorantMeasure J) := by
  intro b π hb hπ
  let μ := volume.restrict C.domain
  have hbmeas := hb.continuous.measurable.comp C.measurable_paramExtended
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable (fun z => (|(C.multiplicity z : ℝ)| * J z)*|b (C.paramExtended z)|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| * J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [majorantMeasure,integral_densityPush μ C.measurable_paramExtended hρ hρ0 hb.continuous.abs]
  rw [action,ite_eq_left ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand hb (fun i => ⟨1,hπ i⟩)).abs hupper
  filter_upwards [hdet π hπ,C.scalar_ae_paramExtended b] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| * |b (C.paramExtended z)| * |C.jacobian π z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| * |b (C.paramExtended z)|) * J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

end IntegerChart
end SharpIntegralFillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_CurrentAxioms
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

namespace SharpIntegralFillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma scalar_linear (b c : X → ℝ) (a d : ℝ) :
    C.scalar (fun x => a*b x+d*c x) = fun z => a*C.scalar b z+d*C.scalar c z := by
  funext z
  by_cases hz : z ∈ C.domain <;> simp [scalar,hz]

lemma action_linearFirst (b c : X → ℝ) (π : Fin k → X → ℝ) (a d : ℝ)
    (hb : BoundedLip b) (hc : BoundedLip c)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    C.action (fun x => a*b x+d*c x) π = a*C.action b π+d*C.action c π := by
  have hab : Admissible (fun x => a*b x+d*c x) π :=
    ⟨(hb.const_mul a).add (hc.const_mul d),hπ⟩
  rw [action,ite_eq_left hab,action,ite_eq_left ⟨hb,hπ⟩,action,ite_eq_left ⟨hc,hπ⟩,C.scalar_linear]
  have heq : (fun z => (C.multiplicity z : ℝ) * (a*C.scalar b z+d*C.scalar c z) * C.jacobian π z) =
      fun z => a*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z)+
        d*((C.multiplicity z : ℝ)*C.scalar c z*C.jacobian π z) := by funext z; ring
  rw [heq,integral_add ((C.integrable_action_integrand hb hπ).const_mul a)
    ((C.integrable_action_integrand hc hπ).const_mul d),integral_const_mul,integral_const_mul]

lemma ae_jacobian_linear (π : Fin k → X → ℝ) (i : Fin k) (f : X → ℝ) (a d : ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => a*π i x+d*f x)) z =
        a*C.jacobian π z+d*C.jacobian (Function.update π i f) z := by
  obtain ⟨K,hK⟩ := hπ i
  obtain ⟨L,hL⟩ := hf
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,C.ae_differentiableWithinAt_scalar hK,
    C.ae_differentiableWithinAt_scalar hL] with z hz hdπ hdf
  have hd : fderivWithin ℝ (C.scalar (fun x => a*π i x+d*f x)) C.domain z =
      a • fderivWithin ℝ (C.scalar (π i)) C.domain z +
        d • fderivWithin ℝ (C.scalar f) C.domain z := by
    rw [C.scalar_linear]
    exact ((hdπ.hasFDerivWithinAt.const_mul a).add (hdf.hasFDerivWithinAt.const_mul d)).fderivWithin hz
  rw [C.jacobian_update,C.jacobian_update]
  simp only [hd,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun l j =>
    fderivWithin ℝ (C.scalar (π l)) C.domain z (EuclideanSpace.single j 1)
  let w : Fin k → ℝ := fun j => fderivWithin ℝ (C.scalar f) C.domain z (EuclideanSpace.single j 1)
  change (M.updateRow i (a • M i+d • w)).det = a*M.det+d*(M.updateRow i w).det
  rw [Matrix.det_updateRow_add,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self]

lemma action_linearCoord (b : X → ℝ) (π : Fin k → X → ℝ) (i : Fin k)
    (f : X → ℝ) (a d : ℝ) (h : Admissible b π)
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    C.action b (Function.update π i (fun x => a*π i x+d*f x)) =
      a*C.action b π+d*C.action b (Function.update π i f) := by
  have hup {g : X → ℝ} (hg : ∃ K : ℝ≥0, LipschitzWith K g) :
      Admissible b (Function.update π i g) := by
    refine ⟨h.1,fun j => ?_⟩
    by_cases hji : j=i
    · simpa [hji] using hg
    · simpa [hji] using h.2 j
  have hg : ∃ K : ℝ≥0, LipschitzWith K (fun x => a*π i x+d*f x) := by
    obtain ⟨K,hK⟩ := h.2 i
    obtain ⟨L,hL⟩ := hf
    refine ⟨‖a‖₊ * K + ‖d‖₊ * L,?_⟩
    simpa only [Function.comp_def,smul_eq_mul] using
      ((lipschitzWith_smul a).comp hK).add ((lipschitzWith_smul d).comp hL)
  rw [action,ite_eq_left (hup hg),action,ite_eq_left h,action,ite_eq_left (hup hf)]
  calc
    _ = ∫ z in C.domain, a*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z)+
        d*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian (Function.update π i f) z) := by
      apply integral_congr_ae
      filter_upwards [C.ae_jacobian_linear π i f a d h.2 hf] with z hz
      rw [hz]; ring
    _ = _ := by
      rw [integral_add ((C.integrable_action_integrand h.1 h.2).const_mul a)
        ((C.integrable_action_integrand h.1 (hup hf).2).const_mul d),
        integral_const_mul,integral_const_mul]

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma continuousOn_paramExtended : ContinuousOn C.paramExtended C.domain := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  have hl : LipschitzOnWith L C.paramExtended C.domain := by
    apply lipschitzOnWith_iff_restrict.mpr
    convert hφ using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp [paramExtended,z.2]
  exact hl.continuousOn

lemma action_locality (b : X → ℝ) (π : Fin k → X → ℝ) (h : Admissible b π)
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) : C.action b π = 0 := by
  obtain ⟨i,U,c,hU,hb,hπ⟩ := hloc
  rw [action,ite_eq_left h]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem C.borel] with z hz
  by_cases hbz : C.scalar b z = 0
  · simp [hbz]
  have hext : C.paramExtended z = C.param ⟨z,hz⟩ := by simp [paramExtended,hz]
  have hzU : C.paramExtended z ∈ U := by
    rw [hext]
    apply hb
    simpa [Function.mem_support,C.scalar_eq hz] using hbz
  have hh := (C.continuousOn_paramExtended z hz).preimage_mem_nhdsWithin (hU.mem_nhds hzU)
  have heq : C.scalar (π i) =ᶠ[𝓝[C.domain] z] fun _ => c := by
    filter_upwards [hh,eventually_mem_nhdsWithin] with y hy hys
    rw [C.scalar_eq hys]
    have hye : C.paramExtended y = C.param ⟨y,hys⟩ := by simp [paramExtended,hys]
    exact hπ _ (hye ▸ hy)
  have heqz : C.scalar (π i) z = c := by rw [C.scalar_eq hz]; exact hπ _ (hext ▸ hzU)
  have hd := heq.fderivWithin_eq (𝕜 := ℝ) heqz
  have hd0 : fderivWithin ℝ (C.scalar (π i)) C.domain z = 0 := by
    exact hd.trans (by
      simpa only [Function.const_def,Pi.zero_apply] using
        congrFun (fderivWithin_const (𝕜 := ℝ) (E := Euc k) (s := C.domain) c) z)
  have hdet : C.jacobian π z = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    change fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1) = 0
    rw [hd0]; rfl
  rw [hdet,mul_zero]; rfl

variable [MeasurableSpace X] [BorelSpace X]
lemma action_finiteMass : ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls C.action μ := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  obtain ⟨B,hB,hdet⟩ := coordinateJacobian_uniform_bound L
    (fun j : Fin k => EuclideanSpace.single j (1 : ℝ))
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * B) (volume.restrict C.domain) :=
    C.integrable.abs.mul_const B
  refine ⟨C.majorantMeasure (fun _ => B),densityPush_finite _ _ hρ,?_⟩
  apply C.majorant_controls hρ (Eventually.of_forall fun _ => hB)
  intro π hπ
  have hs (i : Fin k) : LipschitzOnWith L (C.scalar (π i)) C.domain := by
    simpa only [one_mul] using C.scalar_lipschitzOn hφ (hπ i)
  choose F hF heq using fun i => (hs i).extend_real
  filter_upwards [C.ae_jacobian_eq_extensions hF heq] with z hz
  have H := hdet F hF z
  rw [hz]
  have heqdet : Matrix.det (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1)) =
      coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
    rw [coordinateJacobian,← Matrix.det_transpose]; rfl
  simpa only [heqdet,Real.norm_eq_abs] using H

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

lemma action_isMetricCurrent : IsMetricCurrent C.action := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have hd : C.domain = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact isEmptyElim (C.param ⟨z,hz⟩)
    have heq : C.action = fun _ _ => 0 := by
      funext b π
      simp [action,hd]
    rw [heq]
    exact isMetricCurrent_zero _
  · exact {
      offDomain := by intro b π h; simp [action,h]
      linearFirst := C.action_linearFirst
      linearCoord := C.action_linearCoord
      sequentialContinuity := C.action_sequentialContinuity
      locality := C.action_locality
      finiteMass := C.action_finiteMass }

end SharpIntegralFillings.IntegerChart

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_MatrixRows
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

namespace SharpIntegralFillings
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

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Polarization
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

namespace SharpIntegralFillings
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def polarizationMatrix {ι : Type*} (p : Seminorm ℝ E) (b : ι → E) : Matrix ι ι ℝ :=
  fun i j => ((p (b i+b j))^2-(p (b i-b j))^2)/4

end SharpIntegralFillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_CurveSpeed
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

namespace SharpIntegralFillings.MetricDifferentiationDense
variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X] {f : ℝ → X} {K : ℝ≥0}
noncomputable def distanceCoordinate (f : ℝ → X) (q : ℕ) (t : ℝ) : ℝ :=
  dist (f t) (denseSeq X q)

noncomputable def metricSpeed (f : ℝ → X) (t : ℝ) : ℝ :=
  ⨆ q : ℕ, |deriv (distanceCoordinate f q) t|

noncomputable def integratedSpeed (f : ℝ → X) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, metricSpeed f x

def HasMetricDerivAt (f : ℝ → X) (v x : ℝ) : Prop :=
  Tendsto (fun t => dist (f t) (f x) / |t-x|) (𝓝[≠] x) (𝓝 v)

end SharpIntegralFillings.MetricDifferentiationDense

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Directional
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

namespace SharpIntegralFillings.MetricDifferentiation
variable {X : Type*} [MetricSpace X]
noncomputable def signedDistance (c : ℝ → X) (t : ℝ) : ℝ :=
  if 0 ≤ t then dist (c t) (c 0) else -dist (c t) (c 0)

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

noncomputable def scalarCoordinate (f : E → X) (q : ℕ) (x : E) : ℝ :=
  dist (f x) (denseSeq X q)

noncomputable def lineSpeed (f : E → X) (v x : E) : ℝ :=
  ⨆ q : ℕ, |lineDeriv ℝ (scalarCoordinate f q) x v|

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Seminorm
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

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
noncomputable def coordinateSeminorm (f : E → X) (x : E) (q : ℕ) : Seminorm ℝ E :=
  (normSeminorm ℝ ℝ).comp (fderiv ℝ (scalarCoordinate f q) x).toLinearMap

noncomputable def metricSeminorm (f : E → X) (x : E) : Seminorm ℝ E :=
  ⨆ q : ℕ, coordinateSeminorm f x q

end SharpIntegralFillings.MetricDifferentiation

open Filter Set
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Centered
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

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}
noncomputable def metricQuotient (f : E → X) (x : E) (t : ℝ) (v : E) : ℝ :=
  dist (f (x+t • v)) (f x) / |t|

def HasCenteredMetricDifferential (f : E → X) (p : Seminorm ℝ E) (x : E) : Prop :=
  (fun y => dist (f y) (f x) - p (y-x)) =o[𝓝 x] (fun y => y-x)

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ErrorModulus
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

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

noncomputable def metricErrorTerm (f : E → X) (r : ℝ) (q : ℕ) (x : E) : ℝ :=
  if 0 < ‖denseSeq E q‖ ∧ ‖denseSeq E q‖ ≤ r then
    |dist (f (x + denseSeq E q)) (f x) - metricSeminorm f x (denseSeq E q)| / ‖denseSeq E q‖
  else 0

noncomputable def metricErrorModulus (f : E → X) (r : ℝ) (x : E) : ℝ :=
  ⨆ q : ℕ, metricErrorTerm f r q x

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_TwoPoint
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

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

variable {X : Type*} [MetricSpace X]

def HasTwoPointMetricDifferential (f : E → X) (p : Seminorm ℝ E)
    (s : Set E) (x : E) : Prop :=
  (fun q : E × E => dist (f q.1) (f q.2) - p (q.1 - q.2)) =o[𝓝[s ×ˢ s] (x, x)]
    (fun q : E × E => ‖q.1 - x‖ + ‖q.2 - x‖)

end SharpIntegralFillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Comparison
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

namespace SharpIntegralFillings
universe u
section Geometry
variable (X : Type u) [MetricSpace X]

def IsCAT0 : Prop :=
  ∃ segment : X → X → ℝ → X,
    (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
    (∀ x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment x y s) (segment x y t) = |s - t| * dist x y) ∧
    (∀ o x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment o x s) (segment o y t) ^ 2 ≤
        (s * dist o x - t * dist o y) ^ 2 +
          s * t * ((dist x y) ^ 2 - (dist o x - dist o y) ^ 2))

end Geometry

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_HilbertCharts
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

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

def HasCenteredMetricDifferentialWithin (s : Set E) (f : s → X)
    (p : Seminorm ℝ E) (x : s) : Prop :=
  (fun y : s => dist (f y) (f x) - p ((y : E)-(x : E))) =o[𝓝 x]
    (fun y : s => (y : E)-(x : E))

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ScalarBound
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

namespace SharpIntegralFillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

noncomputable def scalarOn {s : Set E} (f : s → X) (u : X → ℝ) (z : E) : ℝ :=
  by classical exact if hz : z ∈ s then u (f ⟨z,hz⟩) else 0

end SharpIntegralFillings.MetricDifferentiation

open Set MeasureTheory
open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakCompactness
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
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

abbrev TestClass (d : ℕ) (K : ℕ) :=
  {p : C(X, ℝ) × (Fin d → C(X, ℝ)) //
    LipschitzWith K p.1 ∧ ‖p.1‖ ≤ K ∧ ∀ i, LipschitzWith K (p.2 i)}

instance testClass_nonempty (d K : ℕ) : Nonempty (TestClass (X := X) d K) := by
  refine ⟨⟨(0, fun _ => 0), ?_⟩⟩
  refine ⟨(LipschitzWith.const 0).weaken (by positivity), ?_, ?_⟩
  · simp
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)

noncomputable def TestClass.eval {d K : ℕ} (T : Functional X d)
    (p : TestClass (X := X) d K) : ℝ := T p.val.1 (fun i => p.val.2 i)

end Foundations

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_MassTests
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
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
abbrev UnitTestClass (d K : ℕ) :=
  {p : TestClass (X := X) d K // ∀ i, LipschitzWith 1 (p.val.2 i)}

instance unitTestClass_nonempty (d K : ℕ) : Nonempty (UnitTestClass (X := X) d K) := by
  refine ⟨⟨⟨(0,fun _ => 0),?_,?_,?_⟩,?_⟩⟩
  · exact (LipschitzWith.const 0).weaken (by positivity)
  · simp
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)

end SharpIntegralFillings.Foundations
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_EuclideanSplit
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

namespace SharpIntegralFillings.Prism
abbrev Euc (k : ℕ) := EuclideanSpace ℝ (Fin k)

noncomputable def splitLinear (k : ℕ) : Euc (k+1) ≃ₗ[ℝ] ℝ × Euc k where
  toFun z := (z 0, WithLp.toLp 2 (fun i => z i.succ))
  invFun p := WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2))
  left_inv z := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by aesop
  map_add' z w := by ext <;> rfl
  map_smul' a z := by ext <;> rfl

noncomputable def split (k : ℕ) : Euc (k+1) ≃L[ℝ] ℝ × Euc k :=
  (splitLinear k).toContinuousLinearEquiv

@[simp] lemma split_apply (k : ℕ) (z : Euc (k+1)) :
    split k z = (z 0, WithLp.toLp 2 (fun i => z i.succ)) := rfl

@[simp] lemma split_symm_apply (k : ℕ) (p : ℝ × Euc k) :
    (split k).symm p = WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2)) := rfl

end SharpIntegralFillings.Prism

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateChart
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

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
noncomputable def coordinateLayer (k : ℕ) (t : ℝ) (z : Euc k) : Euc (k+1) :=
  (Prism.split k).symm (t,z)

lemma coordinateLayer_lipschitz (t : ℝ) :
    LipschitzWith ‖(Prism.split k).symm.toContinuousLinearMap‖₊ (coordinateLayer k t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := (Prism.split k).symm.lipschitz.dist_le_mul (t,z) (t,w)
  simpa only [coordinateLayer,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using h

lemma coordinateLayer_antilipschitz (t : ℝ) :
    AntilipschitzWith ‖(Prism.split k).toContinuousLinearMap‖₊ (coordinateLayer k t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := (Prism.split k).lipschitz.dist_le_mul
    (coordinateLayer k t z) (coordinateLayer k t w)
  simpa only [coordinateLayer,ContinuousLinearEquiv.apply_symm_apply,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using h

noncomputable def coordinateDomain (t : ℝ) : Set (Euc k) :=
  coordinateLayer k t ⁻¹' C.domain

lemma measurableSet_coordinateDomain (t : ℝ) : MeasurableSet (C.coordinateDomain t) :=
  C.borel.preimage (coordinateLayer_lipschitz (k := k) t).continuous.measurable

lemma bounded_coordinateDomain (t : ℝ) : Bornology.IsBounded (C.coordinateDomain t) := by
  apply Bornology.IsBounded.subset
    ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × Euc k → Euc k)).isBounded_image
      ((Prism.split k).lipschitz.isBounded_image C.bounded))
  intro z hz
  refine ⟨(t,z),?_,rfl⟩
  exact ⟨coordinateLayer k t z,hz,(Prism.split k).apply_symm_apply (t,z)⟩

noncomputable def coordinateParam (t : ℝ) (z : C.coordinateDomain t) : X :=
  C.param ⟨coordinateLayer k t z,z.2⟩

lemma coordinateParam_lipschitz (t : ℝ) {L : ℝ≥0} (hL : LipschitzWith L C.param) :
    LipschitzWith (L * ‖(Prism.split k).symm.toContinuousLinearMap‖₊) (C.coordinateParam t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := hL.dist_le_mul ⟨coordinateLayer k t z,z.2⟩ ⟨coordinateLayer k t w,w.2⟩
  have hh := (coordinateLayer_lipschitz (k := k) t).dist_le_mul z.val w.val
  change dist (C.coordinateParam t z) (C.coordinateParam t w) ≤ _ at h
  calc
    _ ≤ (L:ℝ) * dist (coordinateLayer k t z) (coordinateLayer k t w) := h
    _ ≤ (L:ℝ) * (‖(Prism.split k).symm.toContinuousLinearMap‖₊ * dist z.val w.val) :=
      mul_le_mul_of_nonneg_left hh L.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq]

lemma coordinateParam_antilipschitz (t : ℝ) {U : ℝ≥0} (hU : AntilipschitzWith U C.param) :
    AntilipschitzWith (‖(Prism.split k).toContinuousLinearMap‖₊ * U) (C.coordinateParam t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := hU.le_mul_dist ⟨coordinateLayer k t z,z.2⟩ ⟨coordinateLayer k t w,w.2⟩
  have hh := (coordinateLayer_antilipschitz (k := k) t).le_mul_dist z.val w.val
  calc
    dist z w ≤ ‖(Prism.split k).toContinuousLinearMap‖₊ *
        dist (coordinateLayer k t z) (coordinateLayer k t w) := hh
    _ ≤ ‖(Prism.split k).toContinuousLinearMap‖₊ *
        ((U:ℝ)*dist (C.coordinateParam t z) (C.coordinateParam t w)) :=
      mul_le_mul_of_nonneg_left h (NNReal.coe_nonneg _)
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc]

lemma coordinateParam_bilipschitz (t : ℝ) : ∃ L U : ℝ≥0,
    LipschitzWith L (C.coordinateParam t) ∧ AntilipschitzWith U (C.coordinateParam t) := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  exact ⟨_,_,C.coordinateParam_lipschitz t hL,C.coordinateParam_antilipschitz t hU⟩

noncomputable def coordinateSlice (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) : IntegerChart X k where
  domain := C.coordinateDomain t
  borel := C.measurableSet_coordinateDomain t
  bounded := C.bounded_coordinateDomain t
  param := C.coordinateParam t
  bilipschitz := C.coordinateParam_bilipschitz t
  multiplicity z := C.multiplicity (coordinateLayer k t z)
  integrable := ht

end SharpIntegralFillings.IntegerChart

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateDerivative
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

namespace SharpIntegralFillings.IntegerChart
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

noncomputable def coordinateSliceTotal (t : ℝ) : IntegerChart X k := by
  classical
  exact if ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)) then C.coordinateSlice t ht
    else coordinateEmptyChart

end SharpIntegralFillings.IntegerChart
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateIntegral
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

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
noncomputable def coordinateMinor (π : Fin k → X → ℝ) (w : Euc (k+1)) : ℝ :=
  (Matrix.of fun i j : Fin k =>
    (fderivWithin ℝ (C.scalar (π i)) C.domain w) (EuclideanSpace.single j.succ 1)).det

end SharpIntegralFillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateCoarea
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
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

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

namespace SharpIntegralFillings.BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrable_boundedLip {b : X → ℝ} (hb : BoundedLip b) : Integrable b μ :=
  hb.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end SharpIntegralFillings.BorelCoefficients
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_BorelAction
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
noncomputable def coefficientLinear (hT : IsMetricCurrent T) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    lipAlgebra (X := X) →ₗ[ℝ] ℝ where
  toFun f := T f.val π
  map_add' f g := by
    change T (fun x => f.val x + g.val x) π = _
    simpa using hT.linearFirst f.val g.val π 1 1 f.property g.property hπ
  map_smul' r f := by
    change T (fun x => r * f.val x) π = _
    simpa using hT.linearFirst f.val f.val π r 0 f.property f.property hπ

lemma coefficientLinear_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (f : lipAlgebra (X := X)) :
    ‖coefficientLinear hT π (fun i => ⟨K i, hK i⟩) f‖ ≤
      (∏ i, (K i : ℝ)) * ‖lipToL1 μ f‖ := by
  rw [norm_lipToL1]
  exact hT.mass_bound hμ f.property K hK

noncomputable def l1Action (hT : IsMetricCurrent T) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) : Lp ℝ 1 μ →L[ℝ] ℝ :=
  (coefficientLinear hT π hπ).extendOfNorm (lipToL1 μ)

lemma l1Action_eq (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (f : lipAlgebra (X := X)) : l1Action μ hT π hπ (lipToL1 μ f) = T f.val π := by
  have hπcopy := hπ
  choose K hK using hπcopy
  exact LinearMap.extendOfNorm_eq (lipToL1_dense μ)
    ⟨∏ i, (K i : ℝ), coefficientLinear_bound μ hT hμ π K hK⟩ f

lemma l1Action_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (b : Lp ℝ 1 μ) :
    |l1Action μ hT π (fun i => ⟨K i, hK i⟩) b| ≤ (∏ i, (K i : ℝ)) * ‖b‖ :=
  LinearMap.norm_extendOfNorm_apply_le (lipToL1_dense μ) _
    (coefficientLinear_bound μ hT hμ π K hK) b

noncomputable def borelAction (hT : IsMetricCurrent T) : Functional X k :=
  fun b π => if hb : Integrable b μ then
    if hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i) then
      l1Action μ hT π hπ (hb.toL1 b) else 0 else 0

lemma borelAction_of_integrable (hT : IsMetricCurrent T) {b : X → ℝ}
    (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT b π = l1Action μ hT π hπ (hb.toL1 b) := by
  simp only [borelAction, dite_eq_left hb, dite_eq_left hπ]

lemma borelAction_eq (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hadm : Admissible b π) :
    borelAction μ hT b π = T b π := by
  let f : lipAlgebra (X := X) := ⟨⟨b, hadm.1.continuous⟩, hadm.1⟩
  have hbeq : (integrable_boundedLip μ hadm.1).toL1 b = lipToL1 μ f := by
    apply Lp.ext
    exact (Integrable.coeFn_toL1 _).trans
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val).symm
  rw [borelAction_of_integrable μ hT (integrable_boundedLip μ hadm.1) π hadm.2, hbeq]
  exact l1Action_eq μ hT hμ π hadm.2 f

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma norm_toL1_integral_abs {b : X → ℝ} (hb : Integrable b μ) :
    ‖hb.toL1 b‖ = ∫ x, |b x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toL1] with x hx
  rw [hx, Real.norm_eq_abs]

lemma borelAction_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |borelAction μ hT b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := by
  rw [borelAction_of_integrable μ hT hb π (fun i => ⟨K i, hK i⟩)]
  simpa only [norm_toL1_integral_abs] using l1Action_bound μ hT hμ π K hK (hb.toL1 b)

lemma borelAction_add (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hb : Integrable b μ) (hc : Integrable c μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (b + c) π = borelAction μ hT b π + borelAction μ hT c π := by
  simp only [borelAction_of_integrable μ hT (hb.add hc) π hπ,
    borelAction_of_integrable μ hT hb π hπ, borelAction_of_integrable μ hT hc π hπ,
    ]
  change l1Action μ hT π hπ (hb.toL1 b + hc.toL1 c) = _
  exact map_add _ _ _

lemma borelAction_smul (hT : IsMetricCurrent T) {b : X → ℝ}
    (hb : Integrable b μ) (π : Fin k → X → ℝ) (r : ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (r • b) π = r * borelAction μ hT b π := by
  simp only [borelAction_of_integrable μ hT (hb.smul r) π hπ,
    borelAction_of_integrable μ hT hb π hπ]
  change l1Action μ hT π hπ (r • hb.toL1 b) = _
  exact map_smul _ _ _

lemma l1Action_lipschitz (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    LipschitzWith (∏ i, K i) (l1Action μ hT π (fun i => ⟨K i, hK i⟩)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro b c
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  simpa only [Real.norm_eq_abs, NNReal.coe_prod] using l1Action_bound μ hT hμ π K hK (b-c)

lemma borelAction_sequentialContinuity (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (πs : ℕ → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT b (πs j)) atTop (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hLip
  have hKlim (i) : LipschitzWith (K i) (π i) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    exact le_of_tendsto ((hpt i x).dist (hpt i y))
      (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
  have hlim := tendsto_of_lipschitz_dense (l := atTop)
    (fun j => l1Action_lipschitz μ hT hμ (πs j) K (fun i => hK i j))
    (l1Action_lipschitz μ hT hμ π K hKlim) (lipToL1_dense μ)
    (fun f => ?_) (hb.toL1 b)
  · simp only [borelAction_of_integrable μ hT hb _ (fun i => ⟨K i, hK i _⟩),
      borelAction_of_integrable μ hT hb π (fun i => ⟨K i, hKlim i⟩)]
    exact hlim
  · simp only [l1Action_eq μ hT hμ]
    exact hT.sequentialContinuity f.val π πs f.property (fun i => ⟨K i, hK i⟩) hpt

end BorelCoefficients
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_CanonicalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
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

namespace SharpIntegralFillings
namespace MassMeasure
variable {X : Type u} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
noncomputable def weighted (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

variable {k : ℕ} {T : Functional X k}

noncomputable def currentMassMeasure (hT : IsMetricCurrent T) : Measure X :=
  hT.exists_controls_mass_eq.choose

instance currentMassMeasure_finite (hT : IsMetricCurrent T) :
    IsFiniteMeasure (currentMassMeasure hT) :=
  hT.exists_controls_mass_eq.choose_spec.1

lemma currentMassMeasure_controls (hT : IsMetricCurrent T) :
    Controls T (currentMassMeasure hT) :=
  hT.exists_controls_mass_eq.choose_spec.2.1

end MassMeasure
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeightedAction
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in

lemma toL1_mul_dist_le {f g b : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) :
    ‖(hf.mul_bdd hb hM).toL1 (fun x => f x * b x) -
      (hg.mul_bdd hb hM).toL1 (fun x => g x * b x)‖ ≤
      M * ‖hf.toL1 f - hg.toL1 g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((hf.mul_bdd hb hM).toL1 (fun x => f x * b x))
      ((hg.mul_bdd hb hM).toL1 (fun x => g x * b x)),
    (hf.mul_bdd hb hM).coeFn_toL1, (hg.mul_bdd hb hM).coeFn_toL1,
    Lp.coeFn_sub (hf.toL1 f) (hg.toL1 g), hf.coeFn_toL1, hg.coeFn_toL1, hM]
    with x hsub hfb hgb hsub' hfx hgx hMx
  simp only [Pi.sub_apply] at hsub hsub'
  rw [hsub, hfb, hgb, hsub', hfx, hgx, ← sub_mul, norm_mul]
  nlinarith [norm_nonneg (f x - g x)]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma tendsto_toL1_mul {ι : Type*} {l : Filter ι} {fs : ι → X → ℝ} {f b : X → ℝ}
    (hfs : ∀ j, Integrable (fs j) μ) (hf : Integrable f μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M)
    (hlim : Tendsto (fun j => (hfs j).toL1 (fs j)) l (𝓝 (hf.toL1 f))) :
    Tendsto (fun j => ((hfs j).mul_bdd hb hM).toL1 (fun x => fs j x * b x)) l
      (𝓝 ((hf.mul_bdd hb hM).toL1 (fun x => f x * b x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => toL1_mul_dist_le μ (hfs j) hf hb hM)
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul M

lemma borelAction_locality_mul (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f b : X → ℝ} (hf : Integrable f μ) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧
      Function.support b ⊆ U ∧ ∀ x ∈ U, π i x = c) :
    borelAction μ hT (fun x => f x * b x) π = 0 := by
  obtain ⟨M, hM⟩ := hb.2
  have hbM : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hM x
  have hbmeas := hb.continuous.aestronglyMeasurable (μ := μ)
  obtain ⟨as, has, halim⟩ := mem_closure_iff_seq_limit.mp (lipToL1_dense μ (hf.toL1 f))
  choose fs hfs using has
  have hnorm : Tendsto (fun j => lipToL1 μ (fs j)) atTop (𝓝 (hf.toL1 f)) := by
    simpa only [hfs] using halim
  have hLp (j) : (integrable_boundedLip μ (fs j).property).toL1 (fs j).val =
      lipToL1 μ (fs j) := by
    apply Lp.ext
    exact (Integrable.coeFn_toL1 _).trans
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (fs j).val).symm
  have hnorm' : Tendsto (fun j => (integrable_boundedLip μ (fs j).property).toL1 (fs j).val)
      atTop (𝓝 (hf.toL1 f)) := by simpa only [hLp] using hnorm
  have hprod := tendsto_toL1_mul μ (fun j => integrable_boundedLip μ (fs j).property)
    hf hbmeas hbM hnorm'
  have hact := (l1Action μ hT π hπ).continuous.continuousAt.tendsto.comp hprod
  have hz (j) : l1Action μ hT π hπ
      (((integrable_boundedLip μ (fs j).property).mul_bdd hbmeas hbM).toL1
        (fun x => (fs j).val x * b x)) = 0 := by
    rw [← borelAction_of_integrable μ hT _ π hπ,
      borelAction_eq μ hT hμ ⟨(fs j).property.mul hb, hπ⟩]
    apply hT.locality _ _ ⟨(fs j).property.mul hb, hπ⟩
    obtain ⟨i, U, c, hU, hbU, hc⟩ := hloc
    refine ⟨i, U, c, hU, ?_, hc⟩
    intro x hx
    apply hbU
    change b x ≠ 0
    intro hbx
    exact hx (by simp only [hbx, mul_zero])
  have heq : l1Action μ hT π hπ ((hf.mul_bdd hbmeas hbM).toL1 (fun x => f x * b x)) = 0 :=
    tendsto_nhds_unique hact (by simpa only [Function.comp_def, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rwa [borelAction_of_integrable μ hT (hf.mul_bdd hbmeas hbM) π hπ]

lemma borelAction_linearCoord (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k)
    (g : X → ℝ) (hg : ∃ K : ℝ≥0, LipschitzWith K g) (a c : ℝ) :
    borelAction μ hT b (Function.update π i (fun x => a * π i x + c * g x)) =
      a * borelAction μ hT b π + c * borelAction μ hT b (Function.update π i g) := by
  have hπg : ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i g) j) := by
    intro j
    by_cases hji : j = i
    · simpa only [hji, Function.update_self] using hg
    · simpa only [Function.update_of_ne hji] using hπ j
  have hac : ∃ K : ℝ≥0, LipschitzWith K (fun x => a * π i x + c * g x) := by
    obtain ⟨K, hK⟩ := hπ i
    obtain ⟨L, hL⟩ := hg
    exact ⟨_, (lipschitz_mul_real hK a).add (lipschitz_mul_real hL c)⟩
  have hπac : ∀ j, ∃ K : ℝ≥0,
      LipschitzWith K ((Function.update π i (fun x => a * π i x + c * g x)) j) := by
    intro j
    by_cases hji : j = i
    · simpa only [hji, Function.update_self] using hac
    · simpa only [Function.update_of_ne hji] using hπ j
  have heq : (fun f : Lp ℝ 1 μ =>
      l1Action μ hT (Function.update π i (fun x => a * π i x + c * g x)) hπac f) =
      (fun f => a * l1Action μ hT π hπ f +
        c * l1Action μ hT (Function.update π i g) hπg f) := by
    apply (lipToL1_dense μ).equalizer
    · exact (l1Action μ hT _ _).continuous
    · exact ((l1Action μ hT π hπ).continuous.const_mul a).add
        ((l1Action μ hT _ _).continuous.const_mul c)
    · funext f
      simp only [Function.comp_apply, l1Action_eq μ hT hμ]
      exact hT.linearCoord _ _ i g a c ⟨f.property, hπ⟩ hg
  simpa only [borelAction_of_integrable μ hT hb _ hπac,
    borelAction_of_integrable μ hT hb _ hπ,
    borelAction_of_integrable μ hT hb _ hπg] using congrFun heq (hb.toL1 b)

noncomputable def weightedCurrent (hT : IsMetricCurrent T) (b : X → ℝ) : Functional X k :=
  fun f π => if Admissible f π then borelAction μ hT (fun x => b x * f x) π else 0

lemma weightedCurrent_isMetricCurrent (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) {M : ℝ≥0} (hM : ∀ᵐ x ∂μ, |b x| ≤ M) :
    IsMetricCurrent (weightedCurrent μ hT b) := by
  have hprod {f : X → ℝ} (hf : BoundedLip f) : Integrable (fun x => b x * f x) μ := by
    obtain ⟨N, hN⟩ := hf.2
    exact hb.mul_bdd hf.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hN x)
  have hap {f : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible f π) :
      weightedCurrent μ hT b f π = borelAction μ hT (fun x => b x * f x) π := ite_eq_left h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f π h
    exact ite_eq_right h
  · intro f g π a c hf hg hπ
    rw [hap ⟨(hf.const_mul a).add (hg.const_mul c), hπ⟩,
      hap ⟨hf, hπ⟩, hap ⟨hg, hπ⟩]
    have heq : (fun x => b x * (a * f x + c * g x)) =
        a • (fun x => b x * f x) + c • (fun x => b x * g x) := by funext x; simp <;> ring
    rw [heq, borelAction_add μ hT ((hprod hf).smul a) ((hprod hg).smul c) π hπ,
      borelAction_smul μ hT (hprod hf) π a hπ,
      borelAction_smul μ hT (hprod hg) π c hπ]
  · intro f π i g a c h hg
    have hπg : ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i g) j) := by
      intro j
      by_cases hji : j = i
      · simpa only [hji, Function.update_self] using hg
      · simpa only [Function.update_of_ne hji] using h.2 j
    have hac : ∃ K : ℝ≥0, LipschitzWith K (fun x => a * π i x + c * g x) := by
      obtain ⟨K, hK⟩ := h.2 i
      obtain ⟨L, hL⟩ := hg
      exact ⟨_, (lipschitz_mul_real hK a).add (lipschitz_mul_real hL c)⟩
    have hπac : ∀ j, ∃ K : ℝ≥0,
        LipschitzWith K ((Function.update π i (fun x => a * π i x + c * g x)) j) := by
      intro j
      by_cases hji : j = i
      · simpa only [hji, Function.update_self] using hac
      · simpa only [Function.update_of_ne hji] using h.2 j
    rw [hap ⟨h.1, hπac⟩, hap h, hap ⟨h.1, hπg⟩]
    exact borelAction_linearCoord μ hT hμ (hprod h.1) π h.2 i g hg a c
  · intro f π πs hf hLip hpt
    choose K hK using hLip
    have hπ (i) : LipschitzWith (K i) (π i) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
    simp only [hap ⟨hf, fun i => ⟨K i, hK i _⟩⟩, hap ⟨hf, fun i => ⟨K i, hπ i⟩⟩]
    exact borelAction_sequentialContinuity μ hT hμ (hprod hf) π πs
      (fun i => ⟨K i, hK i⟩) hpt
  · intro f π h hloc
    rw [hap h]
    exact borelAction_locality_mul μ hT hμ hb h.1 π h.2 hloc
  · have hfin : IsFiniteMeasure ((M : ℝ≥0∞) • μ) := by
      constructor
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ univ)
    refine ⟨(M : ℝ≥0∞) • μ, hfin, ?_⟩
    intro f π hf hπ
    rw [hap ⟨hf, fun i => ⟨1, hπ i⟩⟩,
      integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
    have hbound := borelAction_bound μ hT hμ (hprod hf) π (fun _ => 1) hπ
    simp only [NNReal.coe_one, Finset.prod_const_one, one_mul] at hbound
    apply hbound.trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hprod hf).abs ((integrable_boundedLip μ hf).abs.const_mul M)
    filter_upwards [hM] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end BorelCoefficients
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
namespace BorelRestriction
open BorelCoefficients MassMeasure

variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k}
noncomputable def restrictCurrent (hT : IsMetricCurrent T) (E : Set X) : Functional X k :=
  fun b π => if Admissible b π then
    borelAction (currentMassMeasure hT) hT (E.indicator b) π else 0

lemma restrictCurrent_isMetricCurrent (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : IsMetricCurrent (restrictCurrent hT E) := by
  have he : restrictCurrent hT E =
      weightedCurrent (currentMassMeasure hT) hT (E.indicator (fun _ => 1)) := by
    funext b π
    dsimp only [restrictCurrent, weightedCurrent]
    congr 2
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [he]
  apply weightedCurrent_isMetricCurrent _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1 : ℝ)).indicator hE) (M := 1)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E <;> simp [hx]

end BorelRestriction
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_MultiplicityRestriction
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients BorelRestriction MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)

noncomputable def restrictMultiplicity (E : Set X) (hE : MeasurableSet E) : IntegerChart X k :=
  { C with
    multiplicity := (C.paramExtended ⁻¹' E).indicator C.multiplicity
    integrable := by
      have heq : (fun z => (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ)) =
          (C.paramExtended ⁻¹' E).indicator (fun z => (C.multiplicity z : ℝ)) := by
        funext z
        by_cases hz : C.paramExtended z ∈ E <;> simp [hz]
      rw [heq]
      exact C.integrable.indicator (hE.preimage C.measurable_paramExtended) }

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_DomainRestriction
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

namespace SharpIntegralFillings
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

noncomputable def restrictDomain {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) : IntegerChart X k where
  domain := t
  borel := ht
  bounded := C.bounded.subset hts
  param := fun z => C.param ⟨z,hts z.property⟩
  bilipschitz := by
    obtain ⟨K,J,hK,hJ⟩ := C.bilipschitz
    refine ⟨K,J,LipschitzWith.of_dist_le_mul (fun a b =>
      hK.dist_le_mul ⟨a,hts a.property⟩ ⟨b,hts b.property⟩),?_⟩
    exact AntilipschitzWith.of_le_mul_dist (fun a b =>
      hJ.le_mul_dist ⟨a,hts a.property⟩ ⟨b,hts b.property⟩)
  multiplicity := C.multiplicity
  integrable := C.integrable.mono_measure (Measure.restrict_mono hts le_rfl)

end IntegerChart
end SharpIntegralFillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ContainingCharts
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)
noncomputable def withMultiplicity (θ : Euc k → ℤ)
    (hθ : Integrable (fun x => (θ x : ℝ)) (volume.restrict C.domain)) : IntegerChart X k :=
  {C with multiplicity := θ, integrable := hθ}

variable (hCD : C.domain ⊆ D.domain)
  (hparam : ∀ z : C.domain, C.param z = D.param ⟨z,hCD z.property⟩)

include hCD in
lemma indicatorMultiplicity_integrable :
    Integrable (fun x => ((C.domain.indicator C.multiplicity x : ℤ) : ℝ))
      (volume.restrict D.domain) := by
  have hI : IntegrableOn (fun x => (C.multiplicity x : ℝ)) C.domain
      (volume.restrict D.domain) := by
    simpa only [IntegrableOn,Measure.restrict_restrict C.borel,inter_eq_left.mpr hCD] using C.integrable
  apply ((integrable_indicator_iff C.borel).mpr hI).congr
  filter_upwards with x
  by_cases hx : x ∈ C.domain <;> simp [hx]

noncomputable def extendOn : IntegerChart X k :=
  D.withMultiplicity (C.domain.indicator C.multiplicity) (C.indicatorMultiplicity_integrable D hCD)

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ImageRestriction
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
noncomputable def restrictImage (E : Set X) (hE : MeasurableSet E) : IntegerChart X k :=
  C.restrictDomain (C.borel.inter (C.measurable_paramExtended hE)) inter_subset_left

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Summation
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

namespace SharpIntegralFillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma tsum_lintegral_norm_ne_top {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ ≠ ⊤ := by
  have h i : ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hf i).norm]
    simp only [ENNReal.coe_nnreal_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (f i x)))]
  rw [funext h]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hS.abs)

lemma ae_summable_norm_of_integral {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖) := by
  have ht := tsum_lintegral_norm_ne_top hf hS
  rw [←lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)] at ht
  filter_upwards [ae_lt_top' (AEMeasurable.tsum
    (fun i => (hf i).aestronglyMeasurable.enorm)) ht] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

lemma integrable_series_norm {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, ‖f i x‖) μ := by
  refine ⟨by fun_prop,?_⟩
  have hfin : ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ < ⊤ := by
    rw [lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)]
    exact (tsum_lintegral_norm_ne_top hf hS).lt_top
  change (∫⁻ x, ‖∑' i, ‖f i x‖‖ₑ ∂μ) < ⊤
  convert hfin using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr_ae
  filter_upwards [ae_summable_norm_of_integral hf hS] with x hx
  simp_rw [←coe_nnnorm,←NNReal.coe_tsum,enorm_eq_nnnorm,NNReal.nnnorm_eq]
  exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)

lemma integrable_series {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  apply (integrable_series_norm hf hS).mono' (by fun_prop)
  filter_upwards [ae_summable_norm_of_integral hf hS] with x hx
  exact norm_tsum_le_tsum_norm hx

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_IntegerSeries
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

namespace SharpIntegralFillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma intCast_tsum_exists (a : ℕ → ℤ) :
    ∃ z : ℤ, (z : ℝ) = ∑' i, (a i : ℝ) := by
  by_cases h : Summable (fun i => (a i : ℝ))
  · have hm : (∑' i, (a i : ℝ)) ∈ Set.range ((↑) : ℤ → ℝ) := by
      apply Real.isClosed_range_intCast.mem_of_tendsto h.hasSum
      exact Filter.Eventually.of_forall fun s => ⟨∑ i ∈ s, a i,by simp⟩
    exact hm
  · exact ⟨0,by simpa only [Int.cast_zero] using (tsum_eq_zero_of_not_summable h).symm⟩

noncomputable def summedMultiplicity (θ : ℕ → X → ℤ) (x : X) : ℤ :=
  (intCast_tsum_exists (fun i => θ i x)).choose

omit [MeasurableSpace X] in
lemma summedMultiplicity_cast (θ : ℕ → X → ℤ) (x : X) :
    (summedMultiplicity θ x : ℝ) = ∑' i, (θ i x : ℝ) :=
  (intCast_tsum_exists (fun i => θ i x)).choose_spec

lemma summedMultiplicity_integrable {θ : ℕ → X → ℤ}
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) μ)
    (hS : Summable (fun i => ∫ x, |(θ i x : ℝ)| ∂μ)) :
    Integrable (fun x => (summedMultiplicity θ x : ℝ)) μ := by
  simp_rw [summedMultiplicity_cast]
  exact integrable_series hθ (by simpa only [Real.norm_eq_abs] using hS)

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Orientation
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
noncomputable def differentialOrientation (d : ℝ) : ℤ := if 0 ≤ d then 1 else -1

lemma abs_mul_differentialOrientation (d : ℝ) :
    |d| * (differentialOrientation d : ℝ) = d := by
  by_cases hd : 0 ≤ d
  · simp [differentialOrientation,hd,abs_of_nonneg hd]
  · simp [differentialOrientation,hd,abs_of_neg (lt_of_not_ge hd)]

lemma integrableOn_oriented_multiplicity_image {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {θ : E → ℤ} (hθ : IntegrableOn (fun x => (θ x : ℝ)) s μ) :
    IntegrableOn (fun y => ((θ (Function.invFunOn f s y) *
      differentialOrientation (fderivWithin ℝ f s (Function.invFunOn f s y)).det : ℤ) : ℝ))
      (f '' s) μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_within μ hs hf hinj]
  apply (integrable_mul_det_fderivWithin_lipschitzOn μ hs hf hθ).congr
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [hinj.leftInvOn_invFunOn hx,Int.cast_mul,smul_eq_mul]
  rw [←mul_assoc,mul_comm _ (θ x : ℝ),mul_assoc,abs_mul_differentialOrientation]

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Reparametrization
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))
noncomputable def reparam : IntegerChart X k where
  domain := f '' C.domain
  borel := C.borel.image_of_continuousOn_injOn hf.continuousOn (antilipschitzOn_injOn ha)
  bounded := by
    apply Metric.isBounded_iff.mpr
    refine ⟨(K : ℝ) * diam C.domain,?_⟩
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (hf.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem C.bounded hx hy) K.coe_nonneg)
  param := fun y => C.param ⟨Function.invFunOn f C.domain y,Function.invFunOn_mem y.property⟩
  bilipschitz := by
    obtain ⟨J,U,hJ,hU⟩ := C.bilipschitz
    refine ⟨J * L,K * U,?_,?_⟩
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have h := (lipschitzOn_invFunOn ha).dist_le_mul x x.property y y.property
      exact (hJ.dist_le_mul _ _).trans (by
        simpa only [mul_assoc,NNReal.coe_mul,Subtype.dist_eq] using
          (mul_le_mul_of_nonneg_left h J.coe_nonneg))
    · apply AntilipschitzWith.of_le_mul_dist
      intro x y
      have hx := Function.invFunOn_mem x.property
      have hy := Function.invFunOn_mem y.property
      have h := hf.dist_le_mul _ hx _ hy
      rw [Function.invFunOn_eq x.property,Function.invFunOn_eq y.property] at h
      exact h.trans (by
        simpa only [mul_assoc,NNReal.coe_mul,Subtype.dist_eq] using
          (mul_le_mul_of_nonneg_left (hU.le_mul_dist ⟨_,hx⟩ ⟨_,hy⟩) K.coe_nonneg))
  multiplicity := fun y => C.multiplicity (Function.invFunOn f C.domain y) *
    differentialOrientation (fderivWithin ℝ f C.domain (Function.invFunOn f C.domain y)).det
  integrable := integrableOn_oriented_multiplicity_image volume C.borel hf
    (antilipschitzOn_injOn ha) C.integrable

end IntegerChart

end SharpIntegralFillings
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Transitions
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)
noncomputable def inverseParam (x : X) : Euc k :=
  if hx : x ∈ C.image then (Classical.choose hx : C.domain).val else 0

lemma inverseParam_mem {x : X} (hx : x ∈ C.image) :
    C.inverseParam x ∈ C.domain := by
  simp only [inverseParam,dite_eq_left hx]
  exact (Classical.choose hx).property

noncomputable def transition (z : Euc k) : Euc k :=
  if hz : z ∈ C.domain then D.inverseParam (C.param ⟨z,hz⟩) else 0

lemma transition_apply {z : Euc k} (hz : z ∈ C.domain) :
    C.transition D z = D.inverseParam (C.param ⟨z,hz⟩) := by
  simp only [transition,dite_eq_left hz]

variable (hCD : C.image ⊆ D.image)
include hCD

lemma transition_mem {z : Euc k} (hz : z ∈ C.domain) :
    C.transition D z ∈ D.domain := by
  rw [C.transition_apply D hz]
  exact D.inverseParam_mem (hCD ⟨⟨z,hz⟩,rfl⟩)

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_OverlapSum
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

namespace SharpIntegralFillings
open Set Filter MeasureTheory
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

noncomputable def sumMultiplicities (θ : ℕ → Euc k → ℤ)
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) (volume.restrict C.domain))
    (hS : Summable (fun i => ∫ x in C.domain, |(θ i x : ℝ)|)) : IntegerChart X k :=
  C.withMultiplicity (summedMultiplicity θ) (summedMultiplicity_integrable hθ hS)

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Pushforward
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
namespace CurrentOperations

variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

noncomputable def pushCurrent {k : ℕ} (f : X → Y) (T : Functional X k) : Functional Y k :=
  fun b π => if Admissible b π then T (b ∘ f) (fun i => π i ∘ f) else 0

end CurrentOperations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Postcompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory
open CurrentOperations

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

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Straightening
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace EuclideanStraightening
variable {d : ℕ}
noncomputable def replaceMap (j : Fin d) (g : Euc d → ℝ) (z : Euc d) : Euc d :=
  z + (g z-z j) • EuclideanSpace.single j 1

@[simp] lemma replaceMap_apply (j : Fin d) (g : Euc d → ℝ) (z : Euc d) (i : Fin d) :
    replaceMap j g z i = if i=j then g z else z i := by
  simp only [replaceMap,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,
    smul_eq_mul,mul_ite,mul_one,mul_zero]
  split_ifs with hi
  · subst i; ring
  · ring

noncomputable def switchZero {k : ℕ} (j : Fin (k+1)) : Euc (k+1) ≃ₗᵢ[ℝ] Euc (k+1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)

@[simp] lemma switchZero_apply_zero {k : ℕ} (j : Fin (k+1)) (z : Euc (k+1)) :
    switchZero j z 0 = z j := by
  simp [switchZero,Equiv.piCongrLeft']

noncomputable def straightenMap {k : ℕ} (j : Fin (k+1)) (g : Euc (k+1) → ℝ) :
    Euc (k+1) → Euc (k+1) := switchZero j ∘ replaceMap j g

@[simp] lemma straightenMap_zero {k : ℕ} (j : Fin (k+1)) (g : Euc (k+1) → ℝ) (z : Euc (k+1)) :
    straightenMap j g z 0 = g z := by simp [straightenMap]

end EuclideanStraightening
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Negation
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

namespace IntegerChart
variable (C : IntegerChart X k)
noncomputable def negate : IntegerChart X k :=
  { C with multiplicity := fun z => -C.multiplicity z
           integrable := C.integrable.neg.congr (Eventually.of_forall fun _z => (Int.cast_neg _).symm) }

end IntegerChart

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallCurrent
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace SharpIntegralFillings

namespace Optimality

abbrev UnitBall (d : ℕ) := Metric.closedBall (0 : Euc d) 1

instance instNonemptyElemEucUnitBall (d : ℕ) : Nonempty (UnitBall d) := ⟨⟨0, by simp⟩⟩

noncomputable def ballChart (d : ℕ) : IntegerChart (UnitBall d) d where
  domain := Metric.ball 0 1
  borel := measurableSet_ball
  bounded := Metric.isBounded_ball
  param := fun z => ⟨z.val, show dist z.val 0 ≤ 1 from le_of_lt z.property⟩
  bilipschitz := ⟨1, 1, by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    rfl, by
    intro x y
    simp only [ENNReal.coe_one, one_mul]
    rfl⟩
  multiplicity := fun _ => 1
  integrable := by
    simp only [Int.cast_one]
    exact integrableOn_const (μ := volume) (C := (1:ℝ)) Metric.isBounded_ball.measure_lt_top.ne

end Optimality
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_Profiles
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
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.SmoothCutoff
open Set Filter
open scoped Topology NNReal

noncomputable def profile (a : ℝ≥0) (t x : ℝ) : ℝ :=
  Real.smoothTransition ((a:ℝ) * (x-t))
noncomputable def dprofile (a : ℝ≥0) (t x : ℝ) : ℝ :=
  (a:ℝ) * deriv Real.smoothTransition ((a:ℝ) * (x-t))

end SharpIntegralFillings.SmoothCutoff
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open SmoothCutoff

noncomputable def radiusFunction (d : ℕ) (x : UnitBall d) : ℝ := -‖x.val‖

noncomputable def radialProfile {d : ℕ} (a : ℝ≥0) (t : ℝ) (z : Euc d) : ℝ :=
  profile a t (-‖z‖)

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open SmoothCutoff BorelCoefficients BorelRestriction MassMeasure

noncomputable def innerBallCurrent (d : ℕ) (t : ℝ) : Functional (UnitBall d) d :=
  restrictCurrent (ballChart d).action_isMetricCurrent {x | t < radiusFunction d x}

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open BorelCoefficients BorelRestriction MassMeasure CurrentOperations

noncomputable def ambientCoord {d : ℕ} (i : Fin d) : Euc d → ℝ := EuclideanSpace.proj i
noncomputable def unitCoord {d : ℕ} (i : Fin d) (x : UnitBall d) : ℝ := ambientCoord i x.val

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open CurrentOperations

noncomputable def clippedCoord {d : ℕ} (i : Fin d) (x : Euc d) : ℝ :=
  max (-1) (min 1 (ambientCoord i x))

noncomputable def ambientBall (d : ℕ) (t : ℝ) : Functional (Euc d) d :=
  pushCurrent (fun x : UnitBall d => x.val) (innerBallCurrent d t)

end SharpIntegralFillings.Optimality

end

end OAI
end


