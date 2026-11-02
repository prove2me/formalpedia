-- Prove2me | Definitions.Def_OAIQ093D007
-- name    : OAIQ093D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:05:35.768212+00:00
-- url     : https://prove2.me/theorems/6b702660-24ce-408d-8e2f-015bb524a14e
-- title:
--   Definitions bundle OAIQ093D007 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 101 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure, 2 instances and 70 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanRealShadow`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile`, `OAI.PolycyclicRecognition.CartanWordModel.alternatingCoordinateFamily`, `OAI.PolycyclicRecognition.CartanWordModel.boxBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox`, `OAI.PolycyclicRecognition.CartanWordModel.supportIn`, `OAI.PolycyclicRecognition.CartanWordModel.translatedGroupBoxProbability`, `OAI.PolycyclicRecognition.ComplexCartan.bracketOperator`, `OAI.PolycyclicRecognition.ComplexCartan.coefficientOperator`, `OAI.PolycyclicRecognition.ComplexCartan.imaginaryOperator`, `OAI.PolycyclicRecognition.ComplexCartan.weightOperatorLinear`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.cartanWeightSection`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.weightImaginaryAction`, `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.NilpotentLieExistenceInput`, `OAI.PolycyclicRecognition.SupportDatum.basisTemplateSupport`, `OAI.PolycyclicRecognition.SupportDatum.templateSupport`, `OAI.PolycyclicRecognition.SupportDatum.transport`, `OAI.PolycyclicRecognition.cartanRealShadowSubalgebra`, `OAI.PolycyclicRecognition.columnCoordinates`, `OAI.PolycyclicRecognition.conjugateCartanWeight`, `OAI.PolycyclicRecognition.finiteUniversalLiePolynomial`, `OAI.PolycyclicRecognition.mixedWordSpan`, `OAI.PolycyclicRecognition.realImaginaryDerivation`, `OAI.PolycyclicRecognition.realImaginaryDerivationLinear`, `OAI.PolycyclicRecognition.realImaginaryOperator`, `OAI.PolycyclicRecognition.templateSymmetryGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `Defs_Measure`, `Defs_WordMetric`, `Poincare`, `PolycyclicRecognition_Algebra_BracketWords`, `PolycyclicRecognition_Algebra_ComplexificationRealForm`, `PolycyclicRecognition_Algebra_FiniteBracketWords`, `PolycyclicRecognition_Algebra_FiniteWordBases`, `PolycyclicRecognition_Algebra_MixedWordIdeal`, `PolycyclicRecognition_Algebra_TemplateSymmetries`, `PolycyclicRecognition_Algebra_WordBasisCoordinates`, `PolycyclicRecognition_Analysis_SupportTemplates`, `PolycyclicRecognition_Analysis_SupportTransport`, `PolycyclicRecognition_Geometry_CartanBoxDilation`, `PolycyclicRecognition_Geometry_CartanBoxExponents`, `PolycyclicRecognition_Geometry_CartanBoxScaling`, `PolycyclicRecognition_Geometry_CartanCellProbability`, `PolycyclicRecognition_Geometry_CartanGenerators`, `PolycyclicRecognition_Geometry_CartanGroupBoxes`, `PolycyclicRecognition_Geometry_CartanModel`, `PolycyclicRecognition_Geometry_CartanNeighborRowProfile`, `PolycyclicRecognition_Geometry_CartanProbeChainDilation`, `PolycyclicRecognition_Geometry_CartanRealShadow`, `PolycyclicRecognition_Geometry_CartanSeparatedAlternatingComparison`, `PolycyclicRecognition_Geometry_CartanUniformNeighborLabels`, `PolycyclicRecognition_Geometry_CartanWordModel`, `PolycyclicRecognition_Geometry_ComplexRotationDerivation`, `PolycyclicRecognition_Geometry_ComplexRotationTorus`, `PolycyclicRecognition_Geometry_ConjugateCartanWeights`, `PolycyclicRecognition_Geometry_ExponentialBoxCoordinates`, `PolycyclicRecognition_Geometry_ExponentialCellMass`, `PolycyclicRecognition_Geometry_ExponentialSubsetVolume`, `PolycyclicRecognition_Geometry_FiniteAssociativeBCH`, `PolycyclicRecognition_Geometry_NilpotentLieModel`, `PolycyclicRecognition_Geometry_RealCartanQuotient`, `PolycyclicRecognition_Geometry_RealRotationDerivation`, `PolycyclicRecognition_Geometry_TriangularHeight`, `PolycyclicRecognition_Geometry_WeightRotationDerivation`, `PolycyclicRecognition_Geometry_WeightedBoxVolume`, `PolycyclicRecognition_Geometry_WeightedColumnBasis`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D000`, `OAIQ093D001`, `OAIQ093D002` and `OAIQ093D003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D012`, `OAIQ093D013`, `OAIQ093D014`, `OAIQ093D015` and `OAIQ093D026`; the statements `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.common_affine_on`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.exists_fixed_basis_radius`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_measurable_box_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_template_profile_paths`, `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths`, `OAI_PolycyclicRecognition_CartanWordModel_exists_interval_recurrence_cells_sequence`, `OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_comparison`, `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_height_intrinsic`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le`, `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence`, `OAI.PolycyclicRecognition.affine_of_horizontal_labels`, `OAI_PolycyclicRecognition_affine_profile_of_segment_inequalities`, `OAI.PolycyclicRecognition.cartan_cocycle_polynomial_boxes`, `OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors`, `OAI_PolycyclicRecognition_exists_compact_allowed_cartan_profiles`, `OAI_PolycyclicRecognition_exists_semidirect_box_metric_bound` and `OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved`; the proofs of `GeneratesNS.word_norm_list_prod_le`, `GeneratesNS.word_norm_pow`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.common_affine_on`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart`, `OAI_PolycyclicRecognition_CartanWordModel_exists_directional_visit_bound` and `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001
import Definitions.Def_OAIQ093D002
import Definitions.Def_OAIQ093D003

section
-- module Solutions.OAIQ093_PR.Defs_WordMetric
attribute [-instance] _root_.GeneratesNS.LipschitzH.add _root_.GeneratesNS.LipschitzH.addMonoid _root_.GeneratesNS.LipschitzH.instAddCommGroup _root_.GeneratesNS.LipschitzH.instAddCommMonoid _root_.GeneratesNS.LipschitzH.zero _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.WordDist.instBorelSpace _root_.GeneratesNS.WordDist.instBorelSpaceAddOpp _root_.GeneratesNS.WordDist.instMeasurableSpace _root_.GeneratesNS.WordDist.instMeasureableSpaceOpp _root_.GeneratesNS.WordDist.measureSpace _root_.GeneratesNS.countable_G _root_.GeneratesNS.countable_add_G _root_.GeneratesNS.discreteTopology _root_.GeneratesNS.fintype_closedBall _root_.GeneratesNS.instContinuousInvG _root_.GeneratesNS.instContinuousMulG _root_.GeneratesNS.instFunLikeLipschitzHGReal _root_.GeneratesNS.instIsTopologicalGroupG _root_.GeneratesNS.isometricGMul _root_.GeneratesNS.lipschitzHVectorSpace _root_.GeneratesNS.lipschitzSMul _root_.GeneratesNS.my_add_haar_right_invariant _root_.GeneratesNS.negLipschitzH _root_.GeneratesNS.subLipschithZ _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.GeneratesNS.LipschitzH.add_apply _root_.GeneratesNS.LipschitzH.finset_sum_apply _root_.GeneratesNS.LipschitzH_apply _root_.GeneratesNS.ae_eq_everywhere _root_.GeneratesNS.lipschitz_add_tofun _root_.GeneratesNS.lipschitz_neg_tofun _root_.GeneratesNS.lipschitz_smul_tofun _root_.GeneratesNS.lipschitz_sub_tofun _root_.GeneratesNS.zero_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The `Generates` class and the word metric

The `Generates` class packaging a finitely generated group with a symmetric generating set, the
definition of polynomial growth, and the word norm / word metric on `G` with its `MetricSpace`
@[expose]
instance.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

lemma word_norm_mul_le (x y: G): WordNorm (x * y) ≤ WordNorm x + WordNorm y := by
  nth_rw 1 [WordNorm]
  rw [csInf_le_iff]
  .

    intro n hn
    rw [mem_lowerBounds] at hn
    simp at hn

    obtain ⟨x_l, x_l_prod, x_l_len⟩ := word_norm_prod_self x
    obtain ⟨y_l, y_l_prod, y_l_len⟩ := word_norm_prod_self y

    have concat_prod: (x_l ++ y_l).unattach.prod = x*y := by
      simp [ProdS] at x_l_prod y_l_prod
      simp [x_l_prod, y_l_prod]

    grw [hn (x_l ++ y_l).length (x_l ++ y_l) rfl concat_prod]
    simp
    grind
  . simp
  .
    obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self (x * y)
    use l.length
    simp
    use l


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs_Measure
attribute [-instance] _root_.GeneratesNS.LipschitzH.add _root_.GeneratesNS.LipschitzH.addMonoid _root_.GeneratesNS.LipschitzH.instAddCommGroup _root_.GeneratesNS.LipschitzH.instAddCommMonoid _root_.GeneratesNS.LipschitzH.zero _root_.GeneratesNS.LipschitzH_seminorm _root_.GeneratesNS.fintype_closedBall _root_.GeneratesNS.instFunLikeLipschitzHGReal _root_.GeneratesNS.isometricGMul _root_.GeneratesNS.lipschitzHVectorSpace _root_.GeneratesNS.lipschitzSMul _root_.GeneratesNS.negLipschitzH _root_.GeneratesNS.subLipschithZ _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Topology, measurability and Haar measure on `G`

`G` is discrete, so its Haar measure is the counting measure. This file records the Borel and
measure-space instances and the resulting a.e.-triviality lemmas.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS


-- Use the fact that our measure is the counting measure (since we have the discrete topology),
-- and negating a finite set of points in an additive group leaves the cardinality unchanged
@[expose]
instance myNegInvariant: MeasureTheory.Measure.IsNegInvariant (myHaarAddOpp) := {
  neg_eq_self := by
    rw [my_add_haar_eq_count]
    simp only [MeasureTheory.Measure.neg_eq_self]
}


-- Definition 3.5 in Vikman - a harmonic function on G
-- Note that our multiplication order is swapped: f (s * x) instead of f (x * s)
-- This is needed to make it match up with the result of MeasureTheory.convolution
-- TODO - can we combine these

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Poincare
attribute [-instance] _root_.GeneratesNS.volume_mul_left_invariant _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Poincaré inequality

`poincare_inequality` and the packing-averaged form `lemma_3_25_poincare`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

omit v_wrapper_inst in
lemma ball_x_one_subset (x: G): (Metric.closedBall x 1) ⊆ ((x) • S) ∪ ((MulOpposite.op x • S))  := by
  intro a ha
  simp
  simp at ha
  rw [Set.mem_smul_set]
  simp [dist, WordDist] at ha
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod_self (x * a⁻¹)
  simp [ProdS] at l_prod
  by_cases l_len_eq: l.length = 0
  .
    have l_eq: l = [] := by grind
    simp [l_eq] at l_prod
    rw [eq_comm, mul_inv_eq_one] at l_prod
    left
    use 1
    simp [one_mem]
    grind
  .
    rw [← l_len] at ha
    have l_len_one: l.length = 1 := by grind
    rw [List.length_eq_one_iff] at l_len_one
    obtain ⟨s, hs⟩ := l_len_one
    simp [hs] at l_prod
    right
    use s⁻¹
    simp
    rw [eq_comm, mul_inv_eq_iff_eq_mul] at l_prod

    rw [l_prod]
    refine ⟨?_, ?_⟩
    .
      rw [← Finset.mem_inv']
      rw [← S_eq_Sinv]
      simp
    .
      simp [l_prod]

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BracketWords
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bracket words for the nilpotent box construction

The linear span of evaluated bracket words is exactly the generated Lie
subalgebra. A finite-dimensional generated algebra therefore has a basis
chosen from actual words. Letter counts give the weights of these words,
including for generalized weight vectors.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators
open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem evalBracketWord_mem_lieSpan (X : I → L) (w : FreeMagma I) :
    evalBracketWord X w ∈ LieSubalgebra.lieSpan ℝ L (Set.range X) := by
  induction w using FreeMagma.rec with
  | of i => exact LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
  | mul a b ha hb => exact LieSubalgebra.lie_mem _ ha hb

theorem span_evalBracketWord (X : I → L) :
    Submodule.span ℝ (Set.range (evalBracketWord X)) =
      (LieSubalgebra.lieSpan ℝ L (Set.range X)).toSubmodule := by
  let S := Submodule.span ℝ (Set.range (evalBracketWord X))
  have hbracket : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, rfl⟩ := hy
        exact Submodule.subset_span ⟨a * b, rfl⟩
      | zero => simpa only [lie_zero] using S.zero_mem
      | add y z _ _ hy hz => simpa only [lie_add] using S.add_mem hy hz
      | smul r y _ hy => simpa only [lie_smul] using S.smul_mem r hy
    | zero => intro y _; simpa only [zero_lie] using S.zero_mem
    | add x z _ _ hx hz =>
      intro y hy
      simpa only [add_lie] using S.add_mem (hx y hy) (hz y hy)
    | smul r x _ hx =>
      intro y hy
      simpa only [smul_lie] using S.smul_mem r (hx y hy)
  let K : LieSubalgebra ℝ L := { S with lie_mem' := fun hx hy => hbracket _ hx _ hy }
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro _ ⟨w, rfl⟩
      exact evalBracketWord_mem_lieSpan X w)
  · change LieSubalgebra.lieSpan ℝ L (Set.range X) ≤ K
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨.of i, rfl⟩

/-- No abstract choice of a spanning vector is needed: every selected basis
vector is the evaluation of a bracket word in the supplied generators. -/
theorem exists_bracketWord_basis [FiniteDimensional ℝ L] (X : I → L)
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank ℝ L)) ℝ L,
      ∀ k, ∃ w : FreeMagma I, evalBracketWord X w = b k := by
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range (evalBracketWord X)) := by
    rw [span_evalBracketWord, hX]
    rfl
  let J := (linearIndepOn_empty ℝ (id : L → L)).extend
    (Set.empty_subset (Set.range (evalBracketWord X)))
  let b : Basis J ℝ L := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (Module.finrank ℝ L) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, fun k => ?_⟩
  simpa only [Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
    (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ Set.range b from ⟨_, rfl⟩))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal adjoint characters and the zero-height case

Starting from an actual simultaneous upper triangular basis for the adjoint
action, the diagonal entries are linear characters and kill every bracket.
The resulting canonical height space is zero exactly when the Lie algebra is
nilpotent. This proves the algebraic zero-height branch used in the manuscript;
it does not assume nilpotence from vanishing height.
-/

namespace PolycyclicRecognition

open Module

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

variable [FiniteDimensional ℝ L]

/-- Engel's theorem applied to the faithful restricted adjoint module proves
nilpotence of the common character kernel. -/
theorem kernelIdeal_nilpotent : LieRing.IsNilpotent T.kernelIdeal := by
  have : LieModule.IsNilpotent T.kernelIdeal L :=
    (LieModule.isNilpotent_iff_forall' (R := ℝ)).mpr fun x =>
      T.ad_nilpotent_of_mem_kernel x x.property
  exact (T.kernelIdeal.incl_injective).lieModuleIsNilpotent
    (f := LieHom.id) (g := T.kernelIdeal.incl.toLinearMap) (fun _ _ => rfl)

end TriangularAdjoint
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexificationRealForm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real form inside a complexified Lie algebra

Real and imaginary tensor coordinates detect membership in a complexified
subalgebra. In particular the complexification of the chosen real Cartan
subalgebra is again Cartan; it is preserved by the canonical conjugation.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

/-- Scalar conjugation is the only failure of complex linearity. -/
theorem complexificationConjugation_smul (z : ℂ) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L (z • x) = star z • complexificationConjugation L x := by
  induction x using OAI.tensorInductionOn with
  | tmul w x => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteBracketWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite list containing every nonzero bracket word

A word of depth `k` belongs to the `k`th lower central ideal. Thus a
nilpotency bound gives a finite list containing every nonzero evaluated
word. The depth cutoff avoids choosing a minimal nilpotence class.
-/

noncomputable section

namespace PolycyclicRecognition

open LieModule Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem evalBracketWord_mem_lowerCentralSeries (X : I → L) (w : FreeMagma I) :
    evalBracketWord X w ∈ lowerCentralSeries ℝ L L (bracketWordDepth w) := by
  induction w using FreeMagma.rec with
  | of i => exact LieSubmodule.mem_top _
  | mul a b ha hb =>
    change ⁅evalBracketWord X a, evalBracketWord X b⁆ ∈
      lowerCentralSeries ℝ L L (max (bracketWordDepth a) (bracketWordDepth b) + 1)
    rw [lowerCentralSeries_succ]
    rcases le_total (bracketWordDepth a) (bracketWordDepth b) with hab | hba
    · rw [max_eq_right hab]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hb
    · rw [max_eq_left hba, ← lie_skew]
      have hh : ⁅evalBracketWord X b, evalBracketWord X a⁆ ∈
          ⁅(⊤ : LieIdeal ℝ L), lowerCentralSeries ℝ L L (bracketWordDepth a)⁆ :=
        LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) ha
      exact (⁅(⊤ : LieIdeal ℝ L), lowerCentralSeries ℝ L L (bracketWordDepth a)⁆).neg_mem hh

theorem evalBracketWord_eq_zero_of_depth
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (w : FreeMagma I) (hw : k ≤ bracketWordDepth w) : evalBracketWord X w = 0 := by
  have h := antitone_lowerCentralSeries ℝ L L hw
    (evalBracketWord_mem_lowerCentralSeries X w)
  rw [hk] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteWordBases
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All bases from a finite word list

The indexing type is finite and includes every ordered word basis selected
from the list. Nilpotence proves this family is nonempty for a generating
alphabet, including the zero-dimensional case.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

variable [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]

/-- A basis chosen from all words automatically belongs to the finite list:
any omitted word is zero and therefore cannot be a basis vector. -/
theorem nonempty_wordBasisSelections (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hgen : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    Nonempty (WordBasisSelections X (boundedBracketWords k)) := by
  obtain ⟨b, hb⟩ := exists_bracketWord_basis X hgen
  choose words hwords using hb
  have hm (j : Fin (finrank ℝ L)) : words j ∈ boundedBracketWords k := by
    apply (mem_boundedBracketWords _ _).mpr
    by_contra h
    have hz := evalBracketWord_eq_zero_of_depth X hk (words j) (Nat.le_of_not_lt h)
    exact b.ne_zero j ((hwords j).symm.trans hz)
  exact ⟨⟨fun j => ⟨words j, hm j⟩, b, hwords⟩⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

def mixedWordSpan (X : I → L) (outside : I → Prop) : Submodule ℝ L :=
  Submodule.span ℝ (evalBracketWord X '' {w | IsMixedWord outside w})

theorem eval_mixed_mem_span (X : I → L) (outside : I → Prop)
    {w : FreeMagma I} (hw : IsMixedWord outside w) :
    evalBracketWord X w ∈ mixedWordSpan X outside :=
  Submodule.subset_span ⟨w, hw, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support exponents of compact templates

The support exponent is the finite maximum of word-basis exponents, with
each letter allowed its own supporting point. Balance gives translation
invariance, and segments recover the support norm.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

def basisTemplateSupport (E : Set W) (b : B) : ℝ :=
  ∑ i, (D.multiplicity b i : ℝ) * D.weightSupport E i

def templateSupport (E : Set W) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (D.basisTemplateSupport E)

omit [Nonempty B] in
theorem weight_le_weightSupport {E : Set W} (hE : IsCompact E)
    {x : W} (hx : x ∈ E) (i : I) : D.weight i x ≤ D.weightSupport E i :=
  le_csSup (hE.image (D.weight i).continuous_of_finiteDimensional).bddAbove ⟨x, hx, rfl⟩

omit [Nonempty B] in
theorem exists_weightSupport_point {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (i : I) : ∃ x ∈ E, D.weightSupport E i = D.weight i x :=
  hE.exists_sSup_image_eq hne (D.weight i).continuous_of_finiteDimensional.continuousOn

omit [Nonempty B] in
theorem weightSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (i : I) :
    D.weightSupport ((fun x => x + w) '' E) i = D.weightSupport E i + D.weight i w := by
  let E' := (fun x => x + w) '' E
  have hc : IsCompact E' := hE.image (continuous_id.add_const w)
  have hn : E'.Nonempty := hne.image _
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hne i
  obtain ⟨y, ⟨z, hz, rfl⟩, hsup'⟩ := D.exists_weightSupport_point hc hn i
  apply le_antisymm
  · rw [hsup', map_add]
    linarith [D.weight_le_weightSupport hE hz i]
  · rw [hsup, ← map_add]
    exact D.weight_le_weightSupport hc ⟨x, hx, rfl⟩ i

omit [Nonempty B] [FiniteDimensional ℝ W] in
theorem weightSupport_segment (w : W) (i : I) :
    D.weightSupport (segment ℝ 0 w) i = max 0 (D.weight i w) := by
  unfold weightSupport
  change sSup ((D.weight i).toAffineMap '' segment ℝ 0 w) = _
  rw [image_segment]
  simp only [LinearMap.coe_toAffineMap, map_zero]
  rw [segment_eq_Icc']
  exact csSup_Icc min_le_max

omit [FiniteDimensional ℝ W] in
@[simp] theorem templateSupport_segment (w : W) :
    D.templateSupport (segment ℝ 0 w) = D.segmentSupport w := by
  unfold templateSupport segmentSupport
  congr 1
  funext b
  simp only [basisTemplateSupport, D.weightSupport_segment, basisSupport]

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateSymmetries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite template-preserving group from the manuscript

Preserving the support exponent of every compact convex template is stronger
than preserving only its values on segments. This file keeps those groups
distinct and proves the required inclusion and finiteness.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- The group in equation (support-symmetry-group) of `boxes.tex`. -/
def templateSymmetryGroup (D : SupportDatum W I B) : Subgroup (W ≃ₗ[ℝ] W) where
  carrier := {A | ∀ E : Set W, IsCompact E → E.Nonempty → Convex ℝ E →
    D.templateSupport (A '' E) = D.templateSupport E}
  one_mem' := by
    intro E _ _ _
    simp
  mul_mem' := by
    intro A C hA hC E hc hn hv
    have hh := hA (C '' E) (hc.image C.continuous_of_finiteDimensional)
      (hn.image C) (hv.linear_image C.toLinearMap)
    change D.templateSupport ((fun x => A (C x)) '' E) = _
    simpa only [Set.image_image, Function.comp_def] using hh.trans (hC E hc hn hv)
  inv_mem' := by
    intro A hA E hc hn hv
    have hh := hA (A.symm '' E) (hc.image A.symm.continuous_of_finiteDimensional)
      (hn.image A.symm) (hv.linear_image A.symm.toLinearMap)
    change D.templateSupport (A.symm '' E) = _
    simpa only [Set.image_image, Function.comp_def, LinearEquiv.apply_symm_apply,
      Set.image_id'] using hh.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedColumnBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Maximizing bases and normalized box coefficients

This is the basis-exchange step in the manuscript's box calculus. A nonzero
coefficient permits column replacement. Maximality of the basis weight then
makes the exponential rescaling factor at most one.
-/

noncomputable section

open scoped BigOperators

namespace PolycyclicRecognition

variable {I : Type*} {n : ℕ}

/-- A genuine invertible column basis maximizing the prescribed total weight. -/
def IsMaximizingColumnBasis (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I) : Prop :=
  (columnBasisMatrix v b).det ≠ 0 ∧
    ∀ d : Fin n → I, (columnBasisMatrix v d).det ≠ 0 →
      columnBasisWeight w d ≤ columnBasisWeight w b

/-- A vector with nonzero coordinate at column `j` can replace that column.
The determinant identity is the exact algebraic exchange witness. -/
theorem det_columnBasis_update
    (v : I → Fin n → ℝ) (b : Fin n → I) (y : I) (j : Fin n)
    (c : Fin n → ℝ) (hc : ∀ k, v y k = ∑ i, c i * v (b i) k) :
    (columnBasisMatrix v (Function.update b j y)).det =
      c j * (columnBasisMatrix v b).det := by
  have hm : columnBasisMatrix v (Function.update b j y) =
      (columnBasisMatrix v b).updateCol j (v y) := by
    ext k i
    by_cases hi : i = j <;> simp [columnBasisMatrix, Matrix.updateCol, hi]
  rw [hm]
  have hv : v y = fun k => ∑ i, c i • columnBasisMatrix v b k i := by
    funext k
    simpa only [smul_eq_mul, columnBasisMatrix] using hc k
  rw [hv, Matrix.det_updateCol_sum, smul_eq_mul]

/-- Maximal total weight gives domination whenever the coordinate is nonzero. -/
theorem weight_le_of_nonzero_coordinate
    (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I)
    (hb : IsMaximizingColumnBasis v w b) (y : I) (j : Fin n)
    (c : Fin n → ℝ) (hc : ∀ k, v y k = ∑ i, c i * v (b i) k)
    (hcj : c j ≠ 0) : w y ≤ w (b j) := by
  have hd : (columnBasisMatrix v (Function.update b j y)).det ≠ 0 := by
    rw [det_columnBasis_update v b y j c hc]
    exact mul_ne_zero hcj hb.1
  have h := hb.2 (Function.update b j y) hd
  have hw : (fun i => w (Function.update b j y i)) =
      Function.update (fun i => w (b i)) j (w y) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  unfold columnBasisWeight at h
  rw [hw, Finset.sum_update_of_mem (Finset.mem_univ j)] at h
  simp only [Finset.sdiff_singleton_eq_erase] at h
  have hs := Finset.sum_erase_add Finset.univ (fun i => w (b i)) (Finset.mem_univ j)
  linarith

/-- Scaling a maximizing basis introduces no growth in its coordinate
coefficients. Zero coordinates require no weight comparison. -/
theorem normalized_coordinate_le
    (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I)
    (hb : IsMaximizingColumnBasis v w b) (y : I) (j : Fin n)
    (c : Fin n → ℝ) (hc : ∀ k, v y k = ∑ i, c i * v (b i) k)
    {r : ℝ} (hr : 0 ≤ r) :
    |c j * Real.exp (r * (w y - w (b j)))| ≤ |c j| := by
  by_cases hz : c j = 0
  · simp [hz]
  have hw := weight_le_of_nonzero_coordinate v w b hb y j c hc hz
  have he : Real.exp (r * (w y - w (b j))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hw))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg (c j))

/-- Coordinates in an invertible selected column basis. The definition also
exists for singular selections, which simplifies the finite uniform bound. -/
def columnCoordinates (v : I → Fin n → ℝ) (b : Fin n → I) (y : I) : Fin n → ℝ :=
  (columnBasisMatrix v b)⁻¹.mulVec (v y)

theorem columnCoordinates_repr (v : I → Fin n → ℝ) (b : Fin n → I)
    (hb : (columnBasisMatrix v b).det ≠ 0) (y : I) (k : Fin n) :
    v y k = ∑ i, columnCoordinates v b y i * v (b i) k := by
  have h : (columnBasisMatrix v b).mulVec (columnCoordinates v b y) = v y := by
    unfold columnCoordinates
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb),
      Matrix.one_mulVec]
  simpa only [Matrix.mulVec, dotProduct, columnBasisMatrix, mul_comm] using
    (congrFun h k).symm

/-- A single constant controls every normalized coefficient, uniformly over
all weights, all maximizing bases, and all nonnegative scales. -/
theorem exists_uniform_normalized_coordinate_bound [Fintype I]
    (v : I → Fin n → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : I → ℝ) (b : Fin n → I),
      IsMaximizingColumnBasis v w b → ∀ (y : I) (j : Fin n) (r : ℝ), 0 ≤ r →
        |columnCoordinates v b y j * Real.exp (r * (w y - w (b j)))| ≤ C := by
  classical
  let C : ℝ := ∑ b : Fin n → I, ∑ y : I, ∑ j : Fin n, |columnCoordinates v b y j|
  refine ⟨C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _
  · intro w b hb y j r hr
    apply (normalized_coordinate_le v w b hb y j (columnCoordinates v b y)
      (columnCoordinates_repr v b hb.1 y) hr).trans
    calc
      |columnCoordinates v b y j| ≤ ∑ k : Fin n, |columnCoordinates v b y k| :=
        Finset.single_le_sum (f := fun k : Fin n => |columnCoordinates v b y k|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ z : I, ∑ k : Fin n, |columnCoordinates v b z k| :=
        Finset.single_le_sum (f := fun z : I => ∑ k : Fin n, |columnCoordinates v b z k|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ y)
      _ ≤ C := Finset.single_le_sum
        (f := fun d : Fin n → I => ∑ z : I, ∑ k : Fin n, |columnCoordinates v d z k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordBasisCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing actual word bases

Invertible selections from the coordinate matrix are exactly the actual word
bases. Thus the finite maximizing-basis argument applies to the Lie word list.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (X : I → L) (S : Finset (FreeMagma I))
  (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)

omit [FiniteDimensional ℝ L] in
theorem wordBasis_det_ne_zero (β : WordBasisSelections X S) :
    (columnBasisMatrix (wordListCoordinates X S b₀) β.val).det ≠ 0 := by
  let b := WordBasisSelections.basis X S β
  have he : columnBasisMatrix (wordListCoordinates X S b₀) β.val = b₀.toMatrix b := by
    ext i j
    change b₀.repr (evalBracketWord X (β.val j)) i = b₀.repr (b j) i
    exact congrArg (fun v : L => b₀.repr v i) (WordBasisSelections.eval_words X S β j)
  rw [he]
  let := b₀.invertibleToMatrix b
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible _)

omit [FiniteDimensional ℝ L] in
/-- The matrix coordinates agree with the intrinsic coordinates in the
selected word basis. -/
theorem columnCoordinates_eq_wordBasis_repr (β : WordBasisSelections X S) (y : S) :
    columnCoordinates (wordListCoordinates X S b₀) β.val y =
      (WordBasisSelections.basis X S β).equivFun (evalBracketWord X y) := by
  let b := WordBasisSelections.basis X S β
  have he : columnBasisMatrix (wordListCoordinates X S b₀) β.val = b₀.toMatrix b := by
    ext i j
    exact congrArg (fun v : L => b₀.repr v i) (WordBasisSelections.eval_words X S β j)
  have hi : (b₀.toMatrix b)⁻¹ = b.toMatrix b₀ :=
    Matrix.inv_eq_left_inv (b.toMatrix_mul_toMatrix_flip b₀)
  unfold columnCoordinates
  rw [he, hi]
  exact b₀.toMatrix_mulVec_repr b (evalBracketWord X y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.templateSupport_segment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting support data to the chosen height coordinates -/

namespace PolycyclicRecognition.SupportDatum

variable {V W I B : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [Fintype I] [Fintype B]

/-- Change the linear coordinates on height, retaining the word multiplicities. -/
def transport (D : PolycyclicRecognition.SupportDatum V I B) (e : V ≃ₗ[ℝ] W) :
    PolycyclicRecognition.SupportDatum W I B where
  weight i := (D.weight i).comp e.symm.toLinearMap
  multiplicity := D.multiplicity
  positive := D.positive
  balanced b w := D.balanced b (e.symm w)
  separates w h := by
    have hw := D.separates (e.symm w) h
    simpa only [e.apply_symm_apply, map_zero] using congrArg e hw

@[simp] theorem transport_weight_apply (D : PolycyclicRecognition.SupportDatum V I B)
    (e : V ≃ₗ[ℝ] W) (i : I) (w : W) :
    (D.transport e).weight i w = D.weight i (e.symm w) := rfl

end PolycyclicRecognition.SupportDatum

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedBoxVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Exact Euclidean volume of the weighted boxes

The determinant separates into the unscaled basis determinant and the
exponential of its total weight. This gives the exact exponential volume
rate of the coordinate box, before passage to nilpotent exponential charts.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PolycyclicRecognition

variable {I : Type*} {n : ℕ}

theorem det_scaledColumnMatrix (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r : ℝ) :
    (scaledColumnMatrix v w b r).det =
      Real.exp (r * columnBasisWeight w b) * (columnBasisMatrix v b).det := by
  change (Matrix.of fun i j => Real.exp (r * w (b j)) * columnBasisMatrix v b i j).det = _
  rw [Matrix.det_mul_row, ← Real.exp_sum]
  congr 2
  exact (Finset.mul_sum _ _ _).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential boxes and the concrete weighted coordinate boxes

The sup-norm definition of a box agrees with the previously measured linear
image of a cube. This identifies group boxes with images of sets having the
exact determinant volume, without treating the two coordinate systems as an
extra hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped Matrix

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Matrix of the scaled word basis in the fixed ambient coordinates. -/
theorem scaledColumnMatrix_eq_basis_toMatrix
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r : ℝ) :
    scaledColumnMatrix (wordListCoordinates X S b₀) cost β.val r =
      b₀.toMatrix (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun i => cost (β.val i)) r) := by
  ext i j
  simp only [scaledColumnMatrix, Basis.toMatrix_apply, exponentialRescaleBasis,
    Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, map_smul, Finsupp.smul_apply,
    smul_eq_mul, wordListCoordinates, Basis.equivFun_apply]
  exact congrArg (fun x : L => Real.exp (r * cost (β.val j)) * b₀.repr x i)
    (WordBasisSelections.eval_words X S β j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent ideal in the Cartan model

Nonzero generalized root vectors lie in the derived algebra. Their generated
ideal is nilpotent for an actual triangular adjoint representation, and its
sum with the Cartan subalgebra is the full Lie algebra.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The Cartan-model ideal is genuinely nilpotent, not assumed nilpotent. -/
theorem cartanRootIdeal_nilpotent [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) : LieRing.IsNilpotent (cartanRootIdeal H) := by
  let := T.kernelIdeal_nilpotent
  exact (LieIdeal.inclusion_injective (cartanRootIdeal_le_kernel H T)).lieAlgebra_isNilpotent

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGenerators
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subalgebra generated by nonzero roots

The subalgebra generated by the nonzero root spaces is already an ideal.
Thus taking the ideal generated by them in the Cartan construction does not
enlarge the subgroup that must later be integrated.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
theorem cartanRootSubalgebra_sup_cartan [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) :
    (cartanRootSubalgebra H).toSubmodule ⊔ H.toSubmodule = ⊤ := by
  let := T.isTriangularizable
  have hroot : (⨆ χ : Weight ℝ H L, ⨆ (_ : χ.IsNonZero), rootSpace H χ) ≤
      cartanRootSubmodule H := by
    apply iSup_le
    intro χ
    apply iSup_le
    intro hχ v hv
    exact LieSubalgebra.subset_lieSpan ⟨χ, hχ, hv⟩
  have hh : H.toLieSubmodule ⊔ cartanRootSubmodule H = ⊤ := by
    apply top_unique
    rw [← cartan_sup_iSup_rootSpace_eq_top (H := H)]
    exact sup_le_sup le_rfl hroot
  have heq := congrArg LieSubmodule.toSubmodule hh
  change H.toSubmodule ⊔ (cartanRootSubalgebra H).toSubmodule = ⊤ at heq
  simpa only [sup_comm] using heq

set_option maxHeartbeats 1000000 in
theorem cartanRootSubalgebra_ideal [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) (x y : L)
    (hy : y ∈ cartanRootSubalgebra H) : ⁅x, y⁆ ∈ cartanRootSubalgebra H := by
  have hx : x ∈ (cartanRootSubalgebra H).toSubmodule ⊔ H.toSubmodule := by
    rw [cartanRootSubalgebra_sup_cartan H T]
    trivial
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_lie]
  exact (cartanRootSubalgebra H).add_mem
    ((cartanRootSubalgebra H).lie_mem hu hy)
    (cartanRootSubalgebra_stable H ⟨v, hv⟩ hy)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cartan word model

The support datum uses all ordered bases selected from a finite list that
contains every nonzero evaluated word. It is therefore attached to the Lie
algebra generators, rather than to an extra family of assumed bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace CartanWordModel

variable {H} (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
instance : Nonempty M.Bases := nonempty_wordBasisSelections M.letter M.bound_zero M.generates

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact box exponents for the Cartan word model

The compact-template support equals the maximum of the determinant exponents
of the actual word boxes. This connects the Lie-algebra construction to the
Euclidean coordinate-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module MeasureTheory
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (e : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Support data in the fixed Euclidean coordinates on height. -/
def supportIn : SupportDatum W (Fin M.letterCount) M.Bases :=
  (M.supportDatum T hunimod).transport e

set_option maxHeartbeats 1000000 in
/-- The exponent of a word is the sum of the separately supported letters. -/
def boxCost (E : Set W) (w : M.wordList) : ℝ :=
  bracketWordExponent ((M.supportIn T hunimod e).weightSupport E) w

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGroupBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group boxes for the Cartan word model

The finite Cartan construction supplies the bases, bracket bounds, nilpotence
and support exponents used here. The only external group facts are the two
explicit published exponential inputs. In particular no box multiplication or
volume estimate is an assumption.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The actual scaled word basis, selected before taking its exponential image. -/
def boxBasis (E : Set W) (β : M.Bases) (r : ℝ) :
    Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H) :=
  exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
    (fun i => M.boxCost T hunimod eW E (β.val i)) r

set_option maxHeartbeats 1000000 in
/-- A Cartan group box is the exponential image of its scaled coordinate cube. -/
def groupBox {G : Type*} (Exp : cartanRootIdeal H → G)
    (E : Set W) (β : M.Bases) (r R : ℝ) : Set G :=
  exponentialCoordinateBox Exp (M.boxBasis T hunimod eW E β r) R

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact template shifts for actual Cartan boxes

The scalar action on generalized weight spaces is a genuine Lie automorphism.
It takes each scaled word basis to the basis for the translated template.
The finite Dynkin identity then integrates it to the needed group automorphism.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped BigOperators Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Translation adds the total word weight to its box exponent. -/
theorem boxCost_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (z : M.wordList) :
    M.boxCost T hunimod eW ((fun x => x + w) '' E) z =
      M.boxCost T hunimod eW E z +
        bracketWordExponent (fun i => M.weight i (cartanHeightSection T H (eW.symm w))) z := by
  unfold boxCost
  have hs : (M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' E) =
      (M.supportIn T hunimod eW).weightSupport E +
        (fun i => M.weight i (cartanHeightSection T H (eW.symm w))) := by
    funext i
    exact (M.supportIn T hunimod eW).weightSupport_translate hE hne w i
  rw [hs, bracketWordExponent_add]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxScaling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homothetic templates and the interior gain for Cartan actions -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

namespace SupportDatum

set_option maxHeartbeats 1000000 in
/-- Positive homotheties scale each letter support exactly. -/
theorem weightSupport_image_smul
    {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B]
    (D : SupportDatum W I B) {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (i : I) :
    D.weightSupport ((fun x => t • x) '' E) i = t * D.weightSupport E i := by
  have hc : IsCompact ((fun x : W => t • x) '' E) :=
    hE.image (continuous_const.smul continuous_id : Continuous (fun x : W => t • x))
  have hn := hne.image (fun x => t • x)
  obtain ⟨x, hx, hs⟩ := D.exists_weightSupport_point hE hne i
  obtain ⟨_, ⟨y, hy, rfl⟩, hs'⟩ := D.exists_weightSupport_point hc hn i
  apply le_antisymm
  · rw [hs', map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (D.weight_le_weightSupport hE hy i) ht
  · rw [hs, ← smul_eq_mul, ← map_smul]
    exact D.weight_le_weightSupport hc ⟨x, hx, rfl⟩ i

end SupportDatum

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Homothety scales every actual word cost, including zero-weight words. -/
theorem boxCost_image_smul {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (w : M.wordList) :
    M.boxCost T hunimod eW ((fun x => t • x) '' E) w =
      t * M.boxCost T hunimod eW E w := by
  simp only [boxCost, bracketWordExponent,
    (M.supportIn T hunimod eW).weightSupport_image_smul hE hne ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option maxHeartbeats 1000000 in
/-- A maximizing basis is unchanged by a nonnegative homothety. -/
theorem maximizing_box_basis_smul
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val) :
    IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW ((fun x => t • x) '' E)) β.val := by
  refine ⟨hβ.1, ?_⟩
  intro γ hγ
  simp only [columnBasisWeight, M.boxCost_image_smul T hunimod eW hE hne ht,
    ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) ht

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The simply connected nilpotent Lie models needed by Cartan factorization

J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013),
Theorem 20.21, p.531, gives the simply connected integration of a finite
dimensional real Lie algebra. For the nilpotent case, exponential coordinates
have a finite polynomial BCH law: F. Baudoin, *An Introduction to the Geometry
of Stochastic Flows* (2004), Appendix B.5–B.6, pp.123–126. These coordinates
give the analytic Lie-group model used here. No metric-growth, Haar-volume,
Cartan-factorization, or quasi-isometry conclusion is included in this input.

The universe of the model can be chosen to match the algebra by using its
finite-dimensional coordinate space (or a lifted copy).
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

universe u

/-- The nilpotent specialization of Lie correspondence in exponential
polynomial coordinates. -/
def NilpotentLieExistenceInput (L : Type u) [LieRing L] [LieAlgebra ℝ L]
    [FiniteDimensional ℝ L] : Prop :=
  LieRing.IsNilpotent L → Nonempty (NilpotentLieModel L)

namespace NilpotentLieModel

variable {L : Type u} [LieRing L] [LieAlgebra ℝ L] (M : NilpotentLieModel L)

/-- Nilpotence is transported to the actual tangent algebra; it is not an
extra assumption about the chosen group. -/
theorem tangent_nilpotent (hnil : LieRing.IsNilpotent L) :
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, M.modelSpace)) M.carrier) :=
  M.equiv.nilpotent_iff_equiv_nilpotent.mp hnil

end NilpotentLieModel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialSubsetVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume of arbitrary subsets in rescaled exponential coordinates

The change-of-coordinates determinant formula applies to the independently
sampled good subset, not just to an entire box. The exponential chart is a
measurable embedding, so this calculation does not assume absolute
continuity of an arbitrarily selected word parametrization.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {I : Type*} {n : ℕ}

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- The full exponential determinant remains valid after discarding any
bad coordinate subset from the independently sampled domain. -/
theorem exponential_rescaled_subset_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (S : Set (Fin (finrank ℝ L) → ℝ)) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) r).equivFun.symm) '' S) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) * volume S := by
  rw [exponential_basis_subset_measure e Exp chart hchart,
    ← scaledColumnMatrix_eq_basis_toMatrix, det_scaledColumnMatrix, abs_mul,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialCellMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite mass of the actual translated exponential cells -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

/-- Every positive finite coordinate cell gives a positive finite Haar cell,
with no restriction on the scale or the deterministic right suffix. -/
theorem translated_exponential_cell_mass
    {L E N I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace N] [ChartedSpace E N] [Group N]
    [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (haar : NilpotentExponentialHaarInput E N)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) N ≃ₜ N) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (k : N)
    (C : Set (Fin (finrank ℝ L) → ℝ)) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ∞) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    let sample := fun y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
      (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm) y * k
    0 < (μ (sample '' C)).toReal ∧ μ (sample '' C) ≠ ∞ := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar e hnil Exp hExp b₀
  let g := (Exp ∘ e) ∘ (exponentialRescaleBasis
    (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm
  have hm : μ ((fun y => g y * k) '' C) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) * volume C := by
    rw [show (fun y => g y * k) '' C = (fun y : N => y * k) '' (g '' C) from
      image_comp (fun y : N => y * k) g C, measure_image_mul_right μ]
    exact exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost r C
  have hd := ENNReal.ofReal_pos.mpr
    (abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β))
  have he := ENNReal.ofReal_pos.mpr (Real.exp_pos (r * columnBasisWeight cost β.val))
  have hzero : μ ((fun y => g y * k) '' C) ≠ 0 := by
    rw [hm]
    exact mul_ne_zero (mul_ne_zero hd.ne' he.ne') hC0
  have hfinite : μ ((fun y => g y * k) '' C) ≠ ∞ := by
    rw [hm]
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top) hCfin.lt_top).ne
  exact ⟨ENNReal.toReal_pos hzero hfinite, hfinite⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCellProbability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability on the actual translated Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
/-- Every translated unit Cartan box is Borel and has positive finite
measure for the same canonical Haar normalization used by recurrence. -/
theorem translated_groupBox_cell_properties
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := (fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
    MeasurableSet Q ∧ μ Q ≠ 0 ∧ μ Q ≠ ∞ := by
  dsimp only
  let b := M.boxBasis T hunimod eW E β r
  let ψ := fun y => ((F.ExpN ∘ F.N.equiv) ∘ b.equivFun.symm) y * k
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  have heq : (fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 =
      ψ '' cube := by
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one, ← image_comp]
    rfl
  rw [heq]
  have hmeas := measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN
    chartN hchartN b k
  have hmass := translated_exponential_cell_mass haarN F.N.equiv (cartanRootIdeal_nilpotent H T)
    F.ExpN F.isExpN chartN hchartN M.letter M.wordList b₀ β
    (M.boxCost T hunimod eW E) r k cube
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
  refine ⟨hmeas.measurableSet_image.mpr measurableSet_Icc, ?_, hmass.2⟩
  exact (ENNReal.toReal_pos_iff.mp hmass.1).1.ne'

set_option maxHeartbeats 1000000 in
/-- The normalized restriction to the actual translated unit box. -/
def translatedGroupBoxProbability
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier) : ProbabilityMeasure F.N.carrier :=
  cellProbabilityMeasure
    (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
    ((fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1)
    (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ E β r k).2.1
    (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ E β r k).2.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSeparatedAlternatingComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated target tuples supply the alternating increment volume

The auxiliary Cartan volume is subexponential. Thus the finite separated
count supplies the full correlated Haar lower bound needed by the product
comparison; this lower bound is not assumed independently.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

set_option maxHeartbeats 1000000 in
def alternatingCoordinateFamily {A : Type*} (h : ℕ) (v₁ v₂ : A) (i : Fin (h * 2)) : A :=
  if (finProdFinEquiv.symm i).2 = 0 then v₁ else v₂

set_option maxHeartbeats 1000000 in
@[simp] theorem alternatingCoordinateFamily_left {A : Type*} (h : ℕ) (v₁ v₂ : A) (j : Fin h) :
    alternatingCoordinateFamily h v₁ v₂ (finProdFinEquiv (j, (0 : Fin 2))) = v₁ := by
  simp [alternatingCoordinateFamily]

set_option maxHeartbeats 1000000 in
@[simp] theorem alternatingCoordinateFamily_right {A : Type*} (h : ℕ) (v₁ v₂ : A) (j : Fin h) :
    alternatingCoordinateFamily h v₁ v₂ (finProdFinEquiv (j, (1 : Fin 2))) = v₂ := by
  simp [alternatingCoordinateFamily]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanUniformNeighborLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform positive threshold for affine neighboring labels -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]


variable [Fintype I] [DecidableEq I] {J : Type*} [Fintype J]

set_option maxHeartbeats 1000000 in
/-- One affine supported pair together with its original sampling data.
The fields record the actual maps, cells, root step and weak law; no
neighbor-label conclusion is included. -/
structure AffineNeighborRow
    (π : G →* Multiplicative W)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (cell : Set W) (βcell : M.Bases)
    (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    {Λ : ℝ≥0} where
  scale : ℕ → ℝ
  grows : Tendsto scale atTop atTop
  pair : ℕ → NormalizedPair G Λ
  center : ℕ → G
  radius : ℕ → ℝ
  radius_nonneg : ∀ n, 0 ≤ radius n
  radius_subexponential : HasSubexponentialUpperBoundSeq scale radius
  base : ℕ → F.N.carrier
  step : ℕ → F.N.carrier
  basis : ℕ → M.Bases
  base_mem : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) (basis n) (scale n) (radius n)
  step_mem : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) (basis n) (scale n) (radius n)
  mode : Fin M.letterCount
  time : ℕ → ℝ
  time_bound : ∀ n, |time n| ≤ radius n * Real.exp
    ((M.weight mode (pivot mode) + δ * B) * scale n)
  root_step : ∀ n, F.inclusionN (step n) =
    ExpG (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  profile : ℕ → F.N.carrier → S × S
  measurable_profile : ∀ n, Measurable (profile n)
  actual : ∀ n q, q ∈ (fun y => y * base n) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (scale n) 1 → ∀ z,
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let br := exponentialRescaleBasis b
      (fun l => bracketWordExponent (fun _ : I => 1) (βD.val l)) (Real.log (scale n))
    (profile n q).1.val z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (Real.log (scale n)) (fun z => ExpG (br.equivFun.symm z)) z ∧
    (profile n q).2.val z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN (q * step n))
      (Real.log (scale n)) (fun z => ExpG (br.equivFun.symm z)) z
  law : ProbabilityMeasure (S × S)
  converges : Tendsto (fun n => ProbabilityMeasure.map
    (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
      cell βcell (scale n) (base n)) (f := (profile n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 law)
  point : S × S
  supported : point ∈ (law : Measure (S × S)).support
  label₁ : templateSymmetryGroup (M.supportIn T hunimod eW)
  label₂ : templateSymmetryGroup (M.supportIn T hunimod eW)
  offset₁ : W
  offset₂ : W
  affine₁ : ∀ z, eW (heightProjection T.character
    ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ) • w) '' interior cell →
    point.1.val z = label₁.val (eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) + offset₁
  affine₂ : ∀ z, eW (heightProjection T.character
    ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - shrink * δ) • w) '' interior cell →
    point.2.val z = label₂.val (eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))) + offset₂

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborRowProfile
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One actual profile map for both cells of an affine neighboring row -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]


variable [Fintype I] [DecidableEq I]


variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

local notation "Q" => fun n => (fun y => y * D.base n) ''
  M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1

set_option maxHeartbeats 1000000 in
/-- Glue the row's two actual profiles using their agreement on overlap. -/
def AffineNeighborRow.gluedProfile (n : ℕ) : F.N.carrier → S :=
  glueNeighborProfile (Q n) (D.step n) (D.profile n)

set_option maxHeartbeats 1000000 in
/-- Gluing preserves the joint law and the actual rescaled formula on both
translated cells. In particular it introduces no new profile hypothesis. -/
theorem AffineNeighborRow.gluedProfile_properties :
    (∀ n, Measurable (D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
      haarN chartN hchartN pivot shrink B δ S n)) ∧
    (∀ n q, q ∈ Q n ∪ (fun y => y * D.step n) '' Q n → ∀ z,
      (D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S n q).val z =
      rescaledMapProfile (fun g => (π ((D.pair n).val.1 g)).toAdd)
        (D.center n) (F.inclusionN q) (Real.log (D.scale n))
        (fun z => ExpG ((exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (Real.log (D.scale n))).equivFun.symm z)) z) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (D.scale n) (D.base n))
      (f := (fun q => (D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
        haarN chartN hchartN pivot shrink B δ S n q,
        D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
          haarN chartN hchartN pivot shrink B δ S n (q * D.step n)))) (((measurable_glueNeighborProfile (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ cell βcell (D.scale n) (D.base n)).1 (D.step n) (D.measurable_profile n)).prodMk ((measurable_glueNeighborProfile (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ cell βcell (D.scale n) (D.base n)).1 (D.step n) (D.measurable_profile n)).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
      atTop (𝓝 D.law) := by
  let value : S → ((Fin (finrank ℝ H) → ℝ) → W) := fun f => f.val
  have hv : Function.Injective value := by
    intro f g h
    apply Subtype.ext
    exact ContinuousMap.ext (congrFun h)
  let actual := fun n q z => rescaledMapProfile
    (fun g => (π ((D.pair n).val.1 g)).toAdd) (D.center n) (F.inclusionN q)
    (Real.log (D.scale n)) (fun z => ExpG ((exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
      (Real.log (D.scale n))).equivFun.symm z)) z
  have hg (n) := glueNeighborProfile_actual (D.step n) (D.profile n) value hv (actual n)
    (fun q hq => funext fun z => (D.actual n q hq z).1)
    (fun q hq => funext fun z => (D.actual n q hq z).2)
  have hmeas (n) := (M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN b₀ cell βcell (D.scale n) (D.base n)).1
  refine ⟨fun n => measurable_glueNeighborProfile (hmeas n) (D.step n)
    (D.measurable_profile n), ?_, ?_⟩
  · intro n q hq z
    exact congrFun ((hg n).2 q hq) z
  · apply D.converges.congr'
    filter_upwards [] with n
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.map_congr
    have hprops := M.translated_groupBox_cell_properties T F hunimod eW
      haarN chartN hchartN b₀ cell βcell (D.scale n) (D.base n)
    filter_upwards [ae_mem_cellProbabilityMeasure
      (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
      (Q n) hprops.1 hprops.2.1 hprops.2.2] with q hq
    exact ((hg n).1 q hq).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProbeChainDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact translation of the normalized probe generator chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The same dilation translates the generator amplitude exponent exactly. -/
theorem probe_dilation_coefficient_bound {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (r t B : ℝ) (i : Fin M.letterCount)
    (ht : |t| ≤ B * Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i)) :
    |t * Real.exp (r * M.weight i (cartanHeightSection T H (eW.symm w)))| ≤
      B * Real.exp (r * (M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' E) i) := by
  rw [(M.supportIn T hunimod eW).weightSupport_translate hE hne w i,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (B * Real.exp (r * (M.supportIn T hunimod eW).weightSupport E i)) *
        Real.exp (r * M.weight i (cartanHeightSection T H (eW.symm w))) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      simp only [supportIn, SupportDatum.transport, supportDatum_weight,
        cartanHeightWeight, LinearMap.comp_apply, LinearEquiv.coe_coe, Weight.toLinear_apply]
      ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexRotationTorus
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact group containing the Cartan rotations

Diagonal unit scalars are invertible on the generalized weight decomposition.
The equations for preserving the bracket and fixing the Cartan algebra cut out
an actual closed subgroup of a finite torus, giving a compact action.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module Set

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- Linear dependence of a block diagonal operator on its coefficients. -/
def weightOperatorLinear : (Weight ℂ H L → ℂ) →ₗ[ℂ] Module.End ℂ L where
  toFun := weightOperator H
  map_add' z w := by
    ext x
    apply root_induction H (x := x)
    · intro χ v hv
      simp only [LinearMap.add_apply, weightOperator_apply H _ χ hv, Pi.add_apply, add_smul]
    · simp
    · intro v w hv hw
      simp only [map_add, LinearMap.add_apply, hv, hw]
  map_smul' r z := by
    ext x
    apply root_induction H (x := x)
    · intro χ v hv
      simp only [LinearMap.smul_apply, weightOperator_apply H _ χ hv, Pi.smul_apply,
        smul_eq_mul, smul_smul, RingHom.id_apply]
    · simp
    · intro v w hv hw
      simp only [map_add, LinearMap.smul_apply, hv, hw]

section Topology

attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.rotationNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.ComplexCartan.rotationNormedSpace
def bracketOperator : L →L[ℂ] (L →L[ℂ] L) :=
  (show L →ₗ[ℂ] (L →L[ℂ] L) from
    { toFun := fun x => Module.End.toContinuousLinearMap (𝕜 := ℂ) L (LieModule.toEnd ℂ L L x)
      map_add' := by intro x y; ext z; exact add_lie x y z
      map_smul' := by intro c x; ext z; exact smul_lie c x z }).toContinuousLinearMap

/-- The continuous operator associated to the finite coefficient vector. -/
def coefficientOperator : (Weight ℂ H L → ℂ) →ₗ[ℂ] (L →L[ℂ] L) :=
  (LinearMap.toContinuousLinearMap : Module.End ℂ L ≃ₗ[ℂ] (L →L[ℂ] L)).toLinearMap.comp
    (weightOperatorLinear H)

@[simp] theorem coefficientOperator_apply (z : Weight ℂ H L → ℂ) (x : L) :
    coefficientOperator H z x = weightOperator H z x := rfl

end Topology
end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConjugateCartanWeights
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation of the complex Cartan weight spaces -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Complex conjugation sends a weight to its conjugate after conjugating
its Cartan argument. -/
def conjugateCartanWeight (χ : complexifiedSubalgebra L H → ℂ) :
    complexifiedSubalgebra L H → ℂ := fun h => star (χ (cartanConjugation L H h))

set_option maxHeartbeats 1000000 in
omit [H.IsCartanSubalgebra] in
theorem conjugation_ad_sub_pow (χ : complexifiedSubalgebra L H → ℂ)
    (h : complexifiedSubalgebra L H) (k : ℕ) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L
      (((toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) (cartanConjugation L H h) -
        χ (cartanConjugation L H h) • 1) ^ k) x) =
      ((toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) h -
        conjugateCartanWeight L H χ h • 1) ^ k) (complexificationConjugation L x) := by
  let A := toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) (cartanConjugation L H h) -
    χ (cartanConjugation L H h) • 1
  let B := toEnd ℂ (complexifiedSubalgebra L H) (ℂ ⊗[ℝ] L) h -
    conjugateCartanWeight L H χ h • 1
  have he (v : ℂ ⊗[ℝ] L) : complexificationConjugation L (A v) =
      B (complexificationConjugation L v) := by
    change complexificationConjugation L
      (⁅(cartanConjugation L H h : ℂ ⊗[ℝ] L), v⁆ - χ (cartanConjugation L H h) • v) =
      ⁅(h : ℂ ⊗[ℝ] L), complexificationConjugation L v⁆ -
        conjugateCartanWeight L H χ h • complexificationConjugation L v
    rw [map_sub, LieEquiv.map_lie, complexificationConjugation_smul]
    change ⁅complexificationConjugation L (complexificationConjugation L h), _⁆ - _ = _
    rw [complexificationConjugation_involutive]
    rfl
  change complexificationConjugation L ((A ^ k) x) = (B ^ k) (complexificationConjugation L x)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, he, ih]

set_option maxHeartbeats 1000000 in
theorem conjugation_mem_genWeightSpace (χ : complexifiedSubalgebra L H → ℂ)
    {x : ℂ ⊗[ℝ] L} (hx : x ∈ genWeightSpace (ℂ ⊗[ℝ] L) χ) :
    complexificationConjugation L x ∈
      genWeightSpace (ℂ ⊗[ℝ] L) (conjugateCartanWeight L H χ) := by
  apply (mem_genWeightSpace _ _ _).mpr
  intro h
  obtain ⟨k, hk⟩ := (mem_genWeightSpace _ _ _).mp hx (cartanConjugation L H h)
  refine ⟨k, ?_⟩
  rw [← conjugation_ad_sub_pow, hk, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealCartanQuotient
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real Cartan representatives of the complex adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

set_option maxHeartbeats 1000000 in
/-- Taking real parts is averaging with the canonical conjugation. -/
theorem complexification_add_conjugate (x : ℂ ⊗[ℝ] L) :
    x + complexificationConjugation L x =
      (complexificationLieHom L) ((2 : ℝ) • complexificationRealPart L x) := by
  induction x using OAI.tensorInductionOn with
  | tmul z y =>
    change z ⊗ₜ[ℝ] y + star z ⊗ₜ[ℝ] y =
      (1 : ℂ) ⊗ₜ[ℝ] ((2 : ℝ) • (z.re • y))
    rw [← TensorProduct.add_tmul, smul_smul, ← TensorProduct.smul_tmul]
    congr 1
    apply Complex.ext <;> simp
    ring
  | add x y hx hy =>
    simp only [map_add, smul_add]
    rw [← hx, ← hy]
    abel

variable {L} {n : ℕ} (T : ComplexTriangularAdjoint L n)

namespace ComplexTriangularAdjoint

set_option maxHeartbeats 1000000 in
/-- The real part of a vector in the complex weight kernel is in the
original real weight kernel. -/
theorem weightMap_realPart_zero {x : ℂ ⊗[ℝ] L}
    (hx : T.complexWeightMap x = 0) :
    T.weightMap (complexificationRealPart L x) = 0 := by
  have hc := T.complexWeightMap_conjugate_zero hx
  have he := congrArg T.complexWeightMap (complexification_add_conjugate L x)
  rw [map_add, hx, hc, zero_add] at he
  have hr : (2 : ℝ) • T.weightMap (complexificationRealPart L x) = 0 := by
    have hr' : T.weightMap ((2 : ℝ) • complexificationRealPart L x) = 0 := he.symm
    simpa only [map_smul] using hr'
  exact (smul_eq_zero.mp hr).resolve_left (by norm_num)

variable [FiniteDimensional ℝ L] (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Every real adjoint-weight vector has a real Cartan representative. -/
theorem exists_real_cartan_representative (x : L) :
    ∃ h : H, T.weightMap h = T.weightMap x := by
  obtain ⟨h, hh⟩ := T.exists_complex_cartan_representative H ((1 : ℂ) ⊗ₜ[ℝ] x)
  have hz : T.complexWeightMap (((1 : ℂ) ⊗ₜ[ℝ] x) - h) = 0 := by
    rw [map_sub, hh, sub_self]
  have hr := T.weightMap_realPart_zero hz
  have hm : complexificationRealPart L (h : ℂ ⊗[ℝ] L) ∈ H :=
    ((mem_complexifiedSubalgebra_iff L H _).mp h.property).1
  refine ⟨⟨complexificationRealPart L h, hm⟩, ?_⟩
  have he : T.weightMap x - T.weightMap (complexificationRealPart L h) = 0 := by
    simpa only [map_sub, complexificationRealPart_tmul, Complex.one_re, one_smul] using hr
  exact (sub_eq_zero.mp he).symm

set_option maxHeartbeats 1000000 in
/-- Surjectivity is onto the actual linear image of the adjoint weights. -/
theorem cartan_weightRange_surjective :
    Function.Surjective (fun h : H => T.weightMap.rangeRestrict (h : L)) := by
  rintro ⟨w, x, rfl⟩
  obtain ⟨h, hh⟩ := T.exists_real_cartan_representative H x
  exact ⟨h, Subtype.ext hh⟩

set_option maxHeartbeats 1000000 in
/-- A linear choice of real Cartan representative for each weight vector. -/
def cartanWeightSection : T.weightMap.range →ₗ[ℝ] H :=
  Classical.choose ((T.weightMap.rangeRestrict.comp H.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (T.cartan_weightRange_surjective H)))

set_option maxHeartbeats 1000000 in
@[simp] theorem cartanWeightSection_weight (w : T.weightMap.range) :
    T.weightMap (T.cartanWeightSection H w : L) = w := by
  have he := Classical.choose_spec
    ((T.weightMap.rangeRestrict.comp H.subtype).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (T.cartan_weightRange_surjective H)))
  exact congrArg Subtype.val (congrArg (fun f : T.weightMap.range →ₗ[ℝ] T.weightMap.range => f w) he)

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexRotationDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The infinitesimal imaginary Cartan action

The infinitesimal compact action is a genuine Lie derivation. Subtracting
it from the original adjoint action removes exactly the imaginary weights.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- Imaginary semisimple part of a Cartan adjoint operator. -/
def imaginaryOperator (h : H) : L →ₗ[ℂ] L :=
  weightOperator H (fun χ => imaginaryPart (χ h))

theorem imaginaryOperator_apply (h : H) (χ : Weight ℂ H L)
    {x : L} (hx : x ∈ genWeightSpace L χ) :
    imaginaryOperator H h x = imaginaryPart (χ h) • x :=
  weightOperator_apply H _ χ hx

theorem imaginaryOperator_apply_genWeight (h : H) (χ : H → ℂ)
    {x : L} (hx : x ∈ genWeightSpace L χ) :
    imaginaryOperator H h x = imaginaryPart (χ h) • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ,LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact imaginaryOperator_apply H h ⟨χ,hχ⟩ hx

/-- The root-bracket rule makes the imaginary semisimple part a derivation. -/
theorem imaginaryOperator_lie (h : H) (x y : L) :
    imaginaryOperator H h ⁅x,y⁆ =
      ⁅imaginaryOperator H h x,y⁆ + ⁅x,imaginaryOperator H h y⁆ := by
  apply root_induction H (x := x)
  · intro χ u hu
    apply root_induction H (x := y)
    · intro ψ v hv
      rw [imaginaryOperator_apply_genWeight H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        imaginaryOperator_apply H h χ hu,imaginaryOperator_apply H h ψ hv]
      simp only [Pi.add_apply,map_add,add_smul,smul_lie,lie_smul]
    · simp
    · intro v w hv hw
      simp only [lie_add,map_add,hv,hw]
      abel
  · simp
  · intro u v hu hv
    simp only [add_lie,map_add,hu,hv]
    abel

@[simp] theorem imaginaryOperator_add (h k : H) (x : L) :
    imaginaryOperator H (h+k) x = imaginaryOperator H h x + imaginaryOperator H k x := by
  apply root_induction H (x := x)
  · intro χ v hv
    simp only [imaginaryOperator_apply H _ χ hv,map_add,add_smul]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]
    abel

@[simp] theorem imaginaryOperator_zero (x : L) : imaginaryOperator H 0 x = 0 := by
  apply root_induction H (x := x)
  · intro χ v hv
    simp only [imaginaryOperator_apply H _ χ hv,map_zero,zero_smul]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,add_zero]

/-- Dependence on the Cartan parameter is real linear. -/
theorem imaginaryOperator_real_smul (r : ℝ) (h : H) (x : L) :
    imaginaryOperator H (r • h) x = r • imaginaryOperator H h x := by
  apply root_induction H (x := x)
  · intro χ v hv
    rw [imaginaryOperator_apply H _ χ hv,imaginaryOperator_apply H _ χ hv,
      LinearMapClass.map_smul_of_tower, map_smul, smul_assoc]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,smul_add]

/-- The imaginary operators commute, including on generalized weight spaces. -/
theorem imaginaryOperator_commute (h k : H) (x : L) :
    imaginaryOperator H h (imaginaryOperator H k x) =
      imaginaryOperator H k (imaginaryOperator H h x) := by
  apply root_induction H (x := x)
  · intro χ v hv
    rw [imaginaryOperator_apply H k χ hv,imaginaryOperator_apply H h χ hv,
      map_smul,map_smul,imaginaryOperator_apply H h χ hv,
      imaginaryOperator_apply H k χ hv,smul_smul,smul_smul,mul_comm]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealRotationDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.realTorusOperator_complexify _root_.OAI.PolycyclicRecognition.realTorusOperator_mul _root_.OAI.PolycyclicRecognition.realTorusOperator_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal Cartan rotations on the real Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Conjugation respects the imaginary semisimple part for real parameters. -/
theorem complex_imaginaryOperator_conjugation (h : H) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L
      (ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H) (realCartanInComplex L H h) x) =
    ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (complexificationConjugation L x) := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    rw [ComplexCartan.imaginaryOperator_apply _ _ χ hv,complexificationConjugation_smul,
      ComplexCartan.imaginaryOperator_apply_genWeight _ _ (conjugateCartanWeight L H χ)
        (conjugation_mem_genWeightSpace L H χ hv)]
    congr 1
    simp [conjugateCartanWeight,ComplexCartan.imaginaryPart]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]

/-- The imaginary operator preserves the embedded real form. -/
theorem exists_real_imaginaryOperator (h : H) (x : L) :
    ∃ y : L, ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) (1 ⊗ₜ[ℝ] x) = 1 ⊗ₜ[ℝ] y := by
  apply (complexification_conjugation_fixed_iff L _).mp
  rw [complex_imaginaryOperator_conjugation]
  simp

/-- The real imaginary semisimple operator, obtained from the actual complex
weight spaces by real descent. -/
def realImaginaryOperator (h : H) : L →ₗ[ℝ] L :=
  (complexificationRealPart L).comp
    ((ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h)).restrictScalars ℝ |>.comp
      (complexificationLieHom L).toLinearMap)

@[simp] theorem realImaginaryOperator_complexify (h : H) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h x =
      ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
        (realCartanInComplex L H h) (1 ⊗ₜ[ℝ] x) := by
  obtain ⟨y,hy⟩ := exists_real_imaginaryOperator L H h x
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L
    (ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) (1 ⊗ₜ[ℝ] x)) = _
  rw [hy,complexificationRealPart_tmul,Complex.one_re,one_smul]

theorem realImaginaryOperator_lie (h : H) (x y : L) :
    realImaginaryOperator L H h ⁅x,y⁆ =
      ⁅realImaginaryOperator L H h x,y⁆ + ⁅x,realImaginaryOperator L H h y⁆ := by
  apply complexificationLieHom_injective L
  simp only [map_add,LieHom.map_lie]
  change (1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h ⁅x,y⁆ =
    ⁅(1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ +
    ⁅(1 : ℂ) ⊗ₜ[ℝ] x,(1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h y⁆
  rw [realImaginaryOperator_complexify,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify]
  simpa only [LieAlgebra.ExtendScalars.bracket_tmul,one_mul] using
    (ComplexCartan.imaginaryOperator_lie (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y))

/-- The infinitesimal compact action as a real derivation. -/
def realImaginaryDerivation (h : H) : LieDerivation ℝ L L where
  toLinearMap := realImaginaryOperator L H h
  leibniz' x y := by
    rw [realImaginaryOperator_lie,← lie_skew (realImaginaryOperator L H h x) y]
    simp only [sub_eq_add_neg,add_comm]

@[simp] theorem realImaginaryOperator_add (h k : H) (x : L) :
    realImaginaryOperator L H (h+k) x = realImaginaryOperator L H h x +
      realImaginaryOperator L H k x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (_ + _)
  rw [TensorProduct.tmul_add,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify,realImaginaryOperator_complexify,
    realCartanInComplex_add,ComplexCartan.imaginaryOperator_add]

@[simp] theorem realImaginaryOperator_zero (x : L) : realImaginaryOperator L H 0 x = 0 := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (0 : L)
  rw [realImaginaryOperator_complexify,realCartanInComplex_zero,
    ComplexCartan.imaginaryOperator_zero,TensorProduct.tmul_zero]

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
/-- The real embedding is linear in the Cartan parameter. -/
theorem realCartanInComplex_real_smul (r : ℝ) (h : H) :
    realCartanInComplex L H (r • h) = r • realCartanInComplex L H h := by
  apply Subtype.ext
  change (1 : ℂ) ⊗ₜ[ℝ] (r • (h : L)) = r • ((1 : ℂ) ⊗ₜ[ℝ] (h : L))
  exact TensorProduct.tmul_smul r 1 (h : L)

theorem realImaginaryOperator_smul (r : ℝ) (h : H) (x : L) :
    realImaginaryOperator L H (r • h) x = r • realImaginaryOperator L H h x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (r • _)
  rw [TensorProduct.tmul_smul,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify,realCartanInComplex_real_smul]
  exact ComplexCartan.imaginaryOperator_real_smul (complexifiedSubalgebra L H) r
    (realCartanInComplex L H h) ((1 : ℂ) ⊗ₜ[ℝ] x)

theorem realImaginaryOperator_commute (h k : H) (x : L) :
    realImaginaryOperator L H h (realImaginaryOperator L H k x) =
      realImaginaryOperator L H k (realImaginaryOperator L H h x) := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realImaginaryOperator_complexify,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify,realImaginaryOperator_complexify]
  exact ComplexCartan.imaginaryOperator_commute _ _ _ _

/-- The imaginary derivation depends linearly on the real Cartan parameter. -/
def realImaginaryDerivationLinear : H →ₗ[ℝ] LieDerivation ℝ L L where
  toFun := realImaginaryDerivation L H
  map_add' h k := by
    ext x
    exact realImaginaryOperator_add L H h k x
  map_smul' r h := by
    ext x
    exact realImaginaryOperator_smul L H r h x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightRotationDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The infinitesimal rotation factors through the complex weight quotient -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra LieModule Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- The infinitesimal imaginary action depends only on the actual weight
quotient; this is the derivative used in the rotational modification. -/
def weightImaginaryAction : L →ₗ[ℝ] LieDerivation ℝ L L :=
  (realImaginaryDerivationLinear L H).comp ((T.cartanWeightSection H).comp
    T.weightMap.rangeRestrict)

@[simp] theorem weightImaginaryAction_kernel (x : L) (hx : T.weightMap x = 0) :
    T.weightImaginaryAction H x = 0 := by
  have he : T.weightMap.rangeRestrict x = 0 := Subtype.ext hx
  change realImaginaryDerivationLinear L H (T.cartanWeightSection H
    (T.weightMap.rangeRestrict x)) = 0
  rw [he,map_zero,map_zero]

@[simp] theorem weightImaginaryAction_lie (x y : L) :
    T.weightImaginaryAction H ⁅x,y⁆ = 0 :=
  T.weightImaginaryAction_kernel H _ (T.weightMap_lie x y)

/-- The infinitesimal rotation acts trivially on the whole weight quotient. -/
theorem weightMap_realImaginaryOperator (h : H) (x : L) :
    T.weightMap (realImaginaryOperator L H h x) = 0 := by
  rw [← T.complexWeightMap_one_tmul,realImaginaryOperator_complexify]
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H)
    (p := fun v => T.complexWeightMap (ComplexCartan.imaginaryOperator
      (complexifiedSubalgebra L H) (realCartanInComplex L H h) v) = 0)
    (x := (1 : ℂ) ⊗ₜ[ℝ] x)
  · intro χ v hv
    rw [ComplexCartan.imaginaryOperator_apply _ _ χ hv,map_smul]
    by_cases hχ : (χ : complexifiedSubalgebra L H → ℂ) = 0
    · have hz : χ (realCartanInComplex L H h) = 0 := congrFun hχ _
      rw [hz,map_zero,zero_smul]
    · rw [T.complexWeightMap_root_zero H hχ hv,smul_zero]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw,add_zero]

@[simp] theorem weightImaginaryAction_annihilate (x y : L) :
    T.weightImaginaryAction H (T.weightImaginaryAction H x y) = 0 := by
  apply T.weightImaginaryAction_kernel H
  exact T.weightMap_realImaginaryOperator H _ _

/-- The quotient derivations commute. -/
theorem weightImaginaryAction_commute (x y : L) :
    ⁅T.weightImaginaryAction H x,T.weightImaginaryAction H y⁆ = 0 := by
  ext z
  change realImaginaryOperator L H _ (realImaginaryOperator L H _ z) -
    realImaginaryOperator L H _ (realImaginaryOperator L H _ z) = 0
  rw [realImaginaryOperator_commute L H,sub_self]

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRealShadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real shadow Lie algebra

Removing only the imaginary semisimple Cartan action gives a genuine Lie
algebra on the original vector space. Its bracket is obtained from a closed
graph in the derivation semidirect sum, so the Jacobi identity is inherited.
-/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The graph of minus the imaginary semisimple derivation. -/
def cartanRealShadowSubalgebra :
    LieSubalgebra ℝ (L ⋊⁅(LieHom.id : LieDerivation ℝ L L →ₗ⁅ℝ⁆ LieDerivation ℝ L L)⁆
      LieDerivation ℝ L L) where
  carrier := {p | p.right = -T.weightImaginaryAction H p.left}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change p.right + q.right = -T.weightImaginaryAction H (p.left+q.left)
    rw [hp,hq,map_add,neg_add]
  smul_mem' r {p} hp := by
    change r • p.right = -T.weightImaginaryAction H (r • p.left)
    rw [hp,map_smul,smul_neg]
  lie_mem' {p q} hp hq := by
    change ⁅p.right,q.right⁆ = -T.weightImaginaryAction H
      (⁅p.left,q.left⁆ + p.right q.left - q.right p.left)
    rw [hp,hq]
    simp only [neg_lie,lie_neg,T.weightImaginaryAction_commute H,
      LieDerivation.neg_apply,map_add,map_sub,map_neg,
      T.weightImaginaryAction_lie H,T.weightImaginaryAction_annihilate H,
      neg_zero,add_zero,sub_zero]

set_option maxHeartbeats 1000000 in
abbrev CartanRealShadow := cartanRealShadowSubalgebra T H

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteAssociativeBCH
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite BCH in an associative algebra with vanishing long products

The universal logarithm constructs the finite Baker--Campbell--Hausdorff
coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

def finiteUniversalLiePolynomial : A :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    ((d.val + 1 : ℚ)⁻¹ * (universalLogarithmCoefficient c n (d.val + 1)).coeff (wordOfFn w)) •
      evalBracketWord X (rightNestedWord d.val w)

end PolycyclicRecognition

end

end OAI
end


