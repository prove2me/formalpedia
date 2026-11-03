-- Prove2me | Definitions.Def_OAIQ093D018
-- name    : OAIQ093D018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:15:34.878523+00:00
-- url     : https://prove2.me/theorems/25c1effe-c334-4081-82be-76930cdfb5ff
-- title:
--   Definitions bundle OAIQ093D018 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 14 definitions and 43 theorems. The definitions and types are `OAI.PolycyclicRecognition.ComplexWeightFactorModel.cartanParameter`, `OAI.PolycyclicRecognition.HasSemisimpleLift`, `OAI.PolycyclicRecognition.commonSemisimpleCentralizer`, `OAI.PolycyclicRecognition.coordinateActionInBasis`, `OAI.PolycyclicRecognition.jointFixedLieSubalgebra`, `OAI.PolycyclicRecognition.leftDynkinTranslationHomeomorph`, `OAI.PolycyclicRecognition.nilpotentModelOfPolynomialIdeal`, `OAI.PolycyclicRecognition.polynomialCoordinateHom`, `OAI.PolycyclicRecognition.polynomialInnerLieEquiv`, `OAI.PolycyclicRecognition.polynomialMatrixLieRepresentation`, `OAI.PolycyclicRecognition.polynomialMatrixRepresentation`, `OAI.PolycyclicRecognition.polynomialModelLieEquiv`, `OAI.PolycyclicRecognition.rightDynkinTranslationHomeomorph`, `OAI.PolycyclicRecognition.semisimpleActionCentralizer`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_BooleanPartitionMaps`, `PolycyclicRecognition_Algebra_CommonSemisimpleCentralizer`, `PolycyclicRecognition_Algebra_ComplexFactorLocalChart`, `PolycyclicRecognition_Algebra_DynkinTranslationHomeomorph`, `PolycyclicRecognition_Algebra_ExtensionSemisimpleCentralizer`, `PolycyclicRecognition_Algebra_FiniteProductGlobalChart`, `PolycyclicRecognition_Algebra_FiniteProductPolynomialCoordinates`, `PolycyclicRecognition_Algebra_FiniteSemisimpleLiftFamily`, `PolycyclicRecognition_Algebra_IntegrationToUnipotentModel`, `PolycyclicRecognition_Algebra_NilpotentCodimensionOneModel`, `PolycyclicRecognition_Algebra_NilpotentPolynomialOperations`, `PolycyclicRecognition_Algebra_NilpotentPolynomialRepresentation`, `PolycyclicRecognition_Algebra_NilpotentPublishedInputs`, `PolycyclicRecognition_Algebra_PolynomialCoordinateIntegration`, `PolycyclicRecognition_Algebra_PolynomialIdealExtensionCoordinates`, `PolycyclicRecognition_Algebra_PolynomialInnerUnipotence`, `PolycyclicRecognition_Algebra_PolynomialMatrixRepresentation`, `PolycyclicRecognition_Algebra_PolynomialModelDynkin`, `PolycyclicRecognition_Algebra_PolynomialModelHom`, `PolycyclicRecognition_Algebra_PolynomialModelRepresentation`, `PolycyclicRecognition_Algebra_PolynomialRepresentationCurves`, `PolycyclicRecognition_Algebra_PolynomialUnipotentModel`, `PolycyclicRecognition_Geometry_DynkinGlobalExponential`, `PolycyclicRecognition_Geometry_NilpotentSemidirectGroup`, `PolycyclicRecognition_Geometry_NormedLiePolynomial`, `PolycyclicRecognition_Geometry_PolynomialMatrixLieRepresentation`, `PolycyclicRecognition_Geometry_SemidirectAxisExponential`, `PolycyclicRecognition_Geometry_SemidirectUnipotentRepresentation`, `PolycyclicRecognition_Geometry_SmoothPolynomialRepresentation`, `PolycyclicRecognition_Lattices_JointFixedSubalgebra`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D012`, `OAIQ093D026`, `OAIQ093D014` and `OAIQ093D015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D020` and `OAIQ093D027`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D012
import Definitions.Def_OAIQ093D026
import Definitions.Def_OAIQ093D014
import Definitions.Def_OAIQ093D015

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanPartitionMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation and split refinement maps for finite Boolean partitions -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool)

theorem booleanPartitionEvaluation_injective (s : Finset I) :
    Function.Injective (booleanPartitionEvaluation a s).hom := by
  intro v w h
  funext c
  have hc := congrArg (fun f : booleanStepRing a => f.val
    (booleanPartitionRepresentative a s c)) h
  change v (booleanPartitionPoint a s (booleanPartitionRepresentative a s c)) =
    w (booleanPartitionPoint a s (booleanPartitionRepresentative a s c)) at hc
  simpa only [booleanPartitionPoint_representative] using hc

theorem booleanPartitionMap_evaluation {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionMap a h ≫ booleanPartitionEvaluation a t =
      booleanPartitionEvaluation a s := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormedLiePolynomial
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth Lie polynomials in a compatible finite-dimensional norm -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L V I : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞ω}

theorem contDiff_normed_finiteDynkinPolynomial {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X : V → Fin n → L)
    (hX : ∀ i, ContDiff ℝ r (fun v => X v i)) :
    ContDiff ℝ r (fun v => finiteDynkinPolynomial coeff (X v)) := by
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro w _
  exact (contDiff_normed_evalBracketWord X hX (rightNestedWord d.val w)).const_smul _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinTranslationHomeomorph
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial homeomorphisms given by BCH translation

Both translations have explicit finite correction inverses. The inverses
also depend continuously on the translating vector.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {c d : ℕ} (coeff : DynkinCoefficients c 2)
  (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
  (hd : lowerCentralSeries ℝ L L d = ⊥)

theorem continuous_binaryDynkin :
    Continuous (fun p : L × L => finiteDynkinPolynomial coeff ![p.1, p.2]) := by
  apply (contDiff_normed_finiteDynkinPolynomial (r := ∞) coeff _ ?_).continuous
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd

def leftDynkinTranslationHomeomorph (a : L) : L ≃ₜ L :=
  homeomorphOfRaisesDifferenceFiltration
    (fun k => (lowerCentralSeries ℝ L L k).toSubmodule) (by simp)
    (congrArg LieSubmodule.toSubmodule hd)
    (fun x => finiteDynkinPolynomial coeff ![a, x])
    ((continuous_binaryDynkin coeff).comp (continuous_const.prodMk continuous_id))
    (binaryDynkin_raises_difference coeff haxis a)

def rightDynkinTranslationHomeomorph (a : L) : L ≃ₜ L :=
  homeomorphOfRaisesDifferenceFiltration
    (fun k => (lowerCentralSeries ℝ L L k).toSubmodule) (by simp)
    (congrArg LieSubmodule.toSubmodule hd)
    (fun x => finiteDynkinPolynomial coeff ![x, a])
    ((continuous_binaryDynkin coeff).comp (continuous_id.prodMk continuous_const))
    (binaryDynkin_raises_left_difference coeff haxis a)

theorem continuous_rightDynkinTranslationInverse :
    Continuous (fun p : L × L => (rightDynkinTranslationHomeomorph coeff haxis hd p.1).symm p.2) := by
  change Continuous (fun p : L × L => filteredNewton
    (fun x => finiteDynkinPolynomial coeff ![x, p.1]) p.2 d)
  exact continuous_parametric_filteredNewton
    (fun a x => finiteDynkinPolynomial coeff ![x, a])
    ((continuous_binaryDynkin coeff).comp (continuous_snd.prodMk continuous_fst)) d

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DynkinGlobalExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global nilpotent exponential coordinates from finite BCH

Finite BCH gives invertible translations on the Lie algebra. Local exponential
coordinates therefore extend to a covering; simple connectedness removes its
fibers. The global-chart assumption is not used.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter Topology
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]

theorem nilpotentGlobalExponentialChart_of_dynkin
    (dynkin : NilpotentDynkinExpansionInput E G) :
    NilpotentGlobalExponentialChartInput E G := by
  intro Exp hExp hnil
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup E), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ E), (inferInstance : LieAlgebra ℝ L) with }
  let finiteL : FiniteDimensional ℝ L := by
    change FiniteDimensional ℝ E
    infer_instance
  let : LocallyPathConnectedSpace L := by
    change LocallyPathConnectedSpace E
    infer_instance
  let : PreconnectedSpace L := by
    change PreconnectedSpace E
    infer_instance
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp d hd 2
  have hmul (x y : L) : Exp (finiteDynkinPolynomial coeff ![x, y]) = Exp x * Exp y := by
    symm
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hprod ![x, y]
  have haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v :=
    finiteDynkinPolynomial_single_of_product hExp coeff hprod
  let lt := @leftDynkinTranslationHomeomorph L (inferInstance : RealNormedLieAlgebra L)
    finiteL _ _ coeff haxis hd
  let rt := @rightDynkinTranslationHomeomorph L (inferInstance : RealNormedLieAlgebra L)
    finiteL _ _ coeff haxis hd
  have hlt0 (a : L) : lt a 0 = a := by
    change finiteDynkinPolynomial coeff ![a, 0] = a
    have heq : ![a, 0] = (Pi.single 0 a : Fin 2 → L) := by
      funext i; fin_cases i <;> simp
    rw [heq, haxis]
  let b := finBasis ℝ L
  obtain ⟨coeffN, _, hprodN⟩ := dynkin Exp hExp d hd (finrank ℝ L)
  obtain ⟨hreg, hder⟩ := local_exponential_regularity_of_dynkin hExp coeffN hprodN b
  let D : (Fin (finrank ℝ L) → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv.trans
    (tangentSpaceCastModel (𝓘(ℝ, E)) (1 : G))
  have hcomb : tangentCombination (E := E) (fun i => (b i : E)) = D.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact (tangentCombination_apply (E := E) (fun i => (b i : E)) x).trans
      (b.equivFun_symm_apply x).symm
  rw [hcomb] at hder
  obtain ⟨hinj, hmap⟩ := locally_injective_open_of_mfderiv_equiv D hreg hder
  let B := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph
  have hmap' : Filter.map Exp (𝓝 (0 : L)) = 𝓝 (1 : G) := by
    calc
      Filter.map Exp (𝓝 (0 : L)) = Filter.map Exp (Filter.map B (𝓝 0)) := by
        rw [B.map_nhds_eq]; simp [B]
      _ = Filter.map (Exp ∘ b.equivFun.symm) (𝓝 0) := Filter.map_map
      _ = 𝓝 (1 : G) := by simpa only [Function.comp_apply, map_zero, hExp.map_zero] using hmap
  have hinj' : ∃ U ∈ 𝓝 (0 : L), InjOn Exp U := by
    obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨B '' U, ?_, ?_⟩
    · have hh := B.isOpenMap.image_mem_nhds hU
      simpa [B] using hh
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
      exact congrArg B (hi hx hy he)
  have hlocal : IsLocalHomeomorph Exp :=
    localHomeomorph_of_translations Exp lt hlt0 hmul hmap' hinj'
  have hright : Continuous (fun p : L × L => rt p.1 p.2) :=
    (@continuous_binaryDynkin L (inferInstance : RealNormedLieAlgebra L) finiteL _ coeff).comp
      (continuous_snd.prodMk continuous_fst)
  have hcov : IsCoveringMap Exp := covering_of_translations Exp rt
    (fun a x => hmul x a) hExp.map_zero hlocal
    (@continuous_rightDynkinTranslationInverse L (inferInstance : RealNormedLieAlgebra L)
      finiteL _ _ coeff haxis hd) hright lt hmul
    (exponential_surjective_of_nilpotent_dynkin dynkin hExp hnil)
  have : LocallyPathConnectedSpace G :=
    (hcov.isQuotientMap (exponential_surjective_of_nilpotent_dynkin dynkin hExp hnil)).locallyPathConnectedSpace
  exact ⟨homeomorphOfSimplyConnectedCovering Exp hcov, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth homomorphisms in polynomial exponential coordinates are linear -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L K : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates K]

def polynomialModelLieEquiv (f : L ≃* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) : L ≃ₗ⁅ℝ⁆ K :=
  LieEquiv.ofBijective (polynomialModelLieHom f.toMonoidHom hf) (by
    have he : (polynomialModelLieHom f.toMonoidHom hf : L → K) = f :=
      funext (polynomialModelLieHom_apply f.toMonoidHom hf)
    rw [he]
    exact f.bijective)

@[simp] theorem polynomialModelLieEquiv_apply (f : L ≃* K)
    (hf : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ f) (x : L) :
    polynomialModelLieEquiv f hf x = f x :=
  polynomialModelLieHom_apply f.toMonoidHom hf x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialInnerUnipotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner perturbations of unipotent nilpotent-group automorphisms

Inner conjugations act trivially on every lower-central quotient. Consequently
multiplying a unipotent automorphism by an arbitrary inner automorphism is
still unipotent, even when the two automorphisms do not commute.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialInnerLieEquiv (w : L) : L ≃ₗ⁅ℝ⁆ L :=
  polynomialModelLieEquiv (MulAut.conj w) ((contMDiff_conjugation w).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

@[simp] theorem polynomialInnerLieEquiv_apply (w x : L) :
    polynomialInnerLieEquiv w x = w * x * w⁻¹ :=
  polynomialModelLieEquiv_apply _ _ x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExtensionSemisimpleCentralizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Semisimple centralizers in a smooth nilpotent-kernel extension

For an abelian quotient, every quotient element has a lift whose conjugation
on the nilpotent kernel centralizes the semisimple part of a prescribed lift.
The correcting element lies in the actual completed kernel.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

def semisimpleActionCentralizer (E : GroupExtension L G Q) (S : L ≃ₗ⁅ℝ⁆ L) : Subgroup G :=
  (Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S}).comap
    E.conjAct

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonSemisimpleCentralizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Common semisimple centralizers in the completed extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

def commonSemisimpleCentralizer (E : GroupExtension L G Q) (ss : List (L ≃ₗ⁅ℝ⁆ L)) :
    Subgroup G := ⨅ T : {T : L ≃ₗ⁅ℝ⁆ L // T ∈ ss}, semisimpleActionCentralizer E T.val

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteProductGlobalChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global exponential charts from one finite product formula

The polynomial degree can be any finite common bound supplied by a concrete
representation. It need not already equal the Lie nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter Topology
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem globalExponentialChart_of_finite_products
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {c : ℕ} (coefficients : (n : ℕ) → DynkinCoefficients c n)
    (products : ∀ n (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G),
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial (coefficients n) X)) :
    ∃ chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, chart x = Exp x := by
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup E), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ E), (inferInstance : LieAlgebra ℝ L) with }
  let finiteL : FiniteDimensional ℝ L := by
    change FiniteDimensional ℝ E
    infer_instance
  let : LocallyPathConnectedSpace L := by
    change LocallyPathConnectedSpace E
    infer_instance
  let : PreconnectedSpace L := by
    change PreconnectedSpace E
    infer_instance
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  let coeff := coefficients 2
  have hprod := products 2
  have hmul (x y : L) : Exp (finiteDynkinPolynomial coeff ![x, y]) = Exp x * Exp y := by
    symm
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hprod ![x, y]
  have haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v :=
    finiteDynkinPolynomial_single_of_product hExp coeff hprod
  let lt := @leftDynkinTranslationHomeomorph L (inferInstance : RealNormedLieAlgebra L)
    finiteL c d coeff haxis hd
  let rt := @rightDynkinTranslationHomeomorph L (inferInstance : RealNormedLieAlgebra L)
    finiteL c d coeff haxis hd
  have hlt0 (a : L) : lt a 0 = a := by
    change finiteDynkinPolynomial coeff ![a, 0] = a
    have heq : ![a, 0] = (Pi.single 0 a : Fin 2 → L) := by
      funext i; fin_cases i <;> simp
    rw [heq, haxis]
  let b := finBasis ℝ L
  let coeffN := coefficients (finrank ℝ L)
  have hprodN := products (finrank ℝ L)
  obtain ⟨hreg, hder⟩ := local_exponential_regularity_of_dynkin hExp coeffN hprodN b
  let D : (Fin (finrank ℝ L) → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv.trans
    (tangentSpaceCastModel (𝓘(ℝ, E)) (1 : G))
  have hcomb : tangentCombination (E := E) (fun i => (b i : E)) = D.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    erw [tangentCombination_apply]
    change (∑ i, x i • b i) = b.equivFun.symm x
    exact (b.equivFun_symm_apply x).symm
  rw [hcomb] at hder
  obtain ⟨hinj, hmap⟩ := locally_injective_open_of_mfderiv_equiv D hreg hder
  let B := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph
  have hmap' : Filter.map Exp (𝓝 (0 : L)) = 𝓝 (1 : G) := by
    calc
      Filter.map Exp (𝓝 (0 : L)) = Filter.map Exp (Filter.map B (𝓝 0)) := by
        rw [B.map_nhds_eq]; simp [B]
      _ = Filter.map (Exp ∘ b.equivFun.symm) (𝓝 0) := Filter.map_map
      _ = 𝓝 (1 : G) := by simpa only [Function.comp_apply, map_zero, hExp.map_zero] using hmap
  have hinj' : ∃ U ∈ 𝓝 (0 : L), InjOn Exp U := by
    obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨B '' U, ?_, ?_⟩
    · have hh := B.isOpenMap.image_mem_nhds hU
      simpa [B] using hh
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
      exact congrArg B (hi hx hy he)
  have hlocal : IsLocalHomeomorph Exp :=
    localHomeomorph_of_translations Exp lt hlt0 hmul hmap' hinj'
  have hright : Continuous (fun p : L × L => rt p.1 p.2) :=
    (@continuous_binaryDynkin L (inferInstance : RealNormedLieAlgebra L) finiteL c coeff).comp
      (continuous_snd.prodMk continuous_fst)
  have hsurj : Function.Surjective Exp :=
    exponential_surjective_of_range_mem_nhds hExp coeff (fun x y => (hmul x y).symm)
      (by rw [← hmap']; exact Filter.range_mem_map)
  have hcov : IsCoveringMap Exp := covering_of_translations Exp rt
    (fun a x => hmul x a) hExp.map_zero hlocal
    (@continuous_rightDynkinTranslationInverse L (inferInstance : RealNormedLieAlgebra L)
      finiteL c d coeff haxis hd) hright lt hmul
    hsurj
  have : LocallyPathConnectedSpace G :=
    (hcov.isQuotientMap hsurj).locallyPathConnectedSpace
  exact ⟨homeomorphOfSimplyConnectedCovering Exp hcov, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful finite-dimensional representation in polynomial coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

theorem polynomialModelProduct_eval (g x : L) (i : Fin n) :
    polynomialModelCoordinate b i (x * g) =
      coordinatePolynomialEvaluation (polynomialModelCoordinate b)
        (polynomialModelProduct b i) g x := by
  rw [polynomialModelCoordinate, P.mul_eq]
  symm
  change (dynkinCoordinatePolynomial b P.coefficients (polynomialModelLetters b) i).eval₂
      (Pi.evalAlgHom ℝ (fun _ : L => ℝ) g).toRingHom (fun j => b.repr x j) = _
  apply eval_dynkinCoordinatePolynomial
  intro k j
  fin_cases k <;> simp [polynomialModelLetters]

theorem finiteDimensional_polynomialModelOrbit :
    FiniteDimensional ℝ (coordinateOrbitSpan (polynomialModelCoordinate b)) :=
  finiteDimensional_coordinateOrbitSpan_of_polynomial (polynomialModelCoordinate b)
    (polynomialModelProduct b) (fun g i x => polynomialModelProduct_eval b g x i)

theorem polynomialModelRepresentation_injective :
    Function.Injective (coordinateOrbitRepresentation (polynomialModelCoordinate b)) := by
  apply coordinateOrbitRepresentation_injective
  intro x y h
  apply b.repr.injective
  ext i
  exact congrFun h i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothPolynomialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness of the polynomial-coordinate representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

theorem contDiff_translated_coordinateFunction {f : L → ℝ}
    (hf : f ∈ coordinateOrbitSpan (polynomialModelCoordinate b)) (a : L) :
    ContDiff ℝ ∞ (fun g => f (a * g)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    have hm : ContDiff ℝ ∞ (fun g : L => (a * g) * h) :=
      ((contMDiff_mul_right (I := 𝓘(ℝ, L)) (a := h)).contDiff).comp
        ((contMDiff_mul_left (I := 𝓘(ℝ, L)) (a := a)).contDiff)
    exact contDiff_pi.mp (b.equivFun.toContinuousLinearEquiv.contDiff.comp hm) i
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (B : W ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

def coordinateActionInBasis : Representation ℝ L W :=
  B.symm.conjRingEquiv.toMonoidHom.comp
    (coordinateOrbitRepresentation (polynomialModelCoordinate b))

omit [FiniteDimensional ℝ W] in
theorem coordinateActionInBasis_eval (g : L) (v : W) (a : L) :
    (B (coordinateActionInBasis b B g v) : L → ℝ) a = (B v : L → ℝ) (a * g) := by
  change (B (B.symm (_)) : L → ℝ) a = _
  rw [B.apply_symm_apply]
  rfl

theorem contDiff_coordinateActionInBasis (v : W) :
    ContDiff ℝ ∞ (fun g => coordinateActionInBasis b B g v) := by
  let e : W →ₗ[ℝ] (L → ℝ) :=
    (coordinateOrbitSpan (polynomialModelCoordinate b)).subtype.comp B.toLinearMap
  have he : Function.Injective e := Subtype.coe_injective.comp B.injective
  apply contDiff_of_coordinateEvaluations e he
  intro a
  have heq : (fun g => e (coordinateActionInBasis b B g v) a) =
      (fun g => (B v : L → ℝ) (a * g)) := by
    funext g
    exact coordinateActionInBasis_eval b B g v a
  rw [heq]
  exact contDiff_translated_coordinateFunction b (B v).2 a

omit [FiniteDimensional ℝ W] in
theorem coordinateActionInBasis_injective : Function.Injective (coordinateActionInBasis b B) :=
  B.symm.conjRingEquiv.injective.comp (polynomialModelRepresentation_injective b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Faithful smooth matrix representations of polynomial exponential models -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

def polynomialMatrixRepresentation : L →* Matrix.GeneralLinearGroup (Fin m) ℝ :=
  (Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom).comp
    (coordinateActionInBasis b B).asGroupHom

theorem polynomialMatrixRepresentation_injective :
    Function.Injective (polynomialMatrixRepresentation b B) := by
  intro x y h
  apply coordinateActionInBasis_injective b B
  apply LinearMap.toMatrixAlgEquiv'.injective
  exact congrArg Units.val h

theorem contDiff_polynomialMatrixRepresentation :
    ContDiff ℝ ∞ (fun g =>
      (polynomialMatrixRepresentation b B g : Matrix (Fin m) (Fin m) ℝ)) := by
  let e : (Fin m → Fin m → ℝ) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    LinearEquiv.refl ℝ _
  have hf : ContDiff ℝ ∞ (fun g => fun i j =>
      coordinateActionInBasis b B g (Pi.single j 1) i) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_pi.mp (contDiff_coordinateActionInBasis b B (Pi.single j 1)) i
  exact e.toContinuousLinearEquiv.contDiff.comp hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialMatrixLieRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie differentials of the polynomial-coordinate representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

def polynomialMatrixLieRepresentation : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ :=
  (unitsHomLieDifferential (polynomialMatrixRepresentation b B)
    (contDiff_polynomialMatrixRepresentation b B).contMDiff).comp P.tangentEquiv.toLieHom

theorem polynomialMatrixLieRepresentation_injective :
    Function.Injective (polynomialMatrixLieRepresentation b B) := by
  have hi := injective_algebra_differential
    PolynomialExponentialCoordinates.isGroupExponential_identity
    (polynomialMatrixRepresentation b B) (polynomialMatrixRepresentation_injective b B)
    (unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff)
  exact hi.comp P.tangentEquiv.injective

theorem polynomialMatrixLieRepresentation_exp (x : L) :
    polynomialMatrixRepresentation b B x =
      algebraExpUnit (polynomialMatrixLieRepresentation b B x) := by
  have h := hom_exp_eq_algebraExpUnit
    PolynomialExponentialCoordinates.isGroupExponential_identity
    (polynomialMatrixRepresentation b B)
    (unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff) (P.tangentEquiv x)
  change polynomialMatrixRepresentation b B (P.tangentEquiv x) =
    algebraExpUnit (polynomialMatrixLieRepresentation b B x) at h
  rwa [P.tangentEquiv_apply] at h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialRepresentationCurves
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial entries along one-parameter subgroups -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)

theorem polynomial_translated_coordinateFunction {f : L → ℝ}
    (hf : f ∈ coordinateOrbitSpan (polynomialModelCoordinate b)) (a v : L) :
    (fun t : ℝ => f (a * (t • v))) ∈ polynomialFunctions := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    exact hasPolynomialLineCoordinates_mul b _ _
      (hasPolynomialLineCoordinates_mul b _ _ (hasPolynomialLineCoordinates_const b a)
        (hasPolynomialLineCoordinates_line b v)) (hasPolynomialLineCoordinates_const b h) i
  | zero => exact polynomialFunctions.zero_mem
  | add f g _ _ hf hg => exact polynomialFunctions.add_mem hf hg
  | smul c f _ hf => exact polynomialFunctions.smul_mem c hf

variable (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

theorem polynomial_coordinateActionInBasis (v : L) (u : Fin m → ℝ) (i : Fin m) :
    (fun t : ℝ => coordinateActionInBasis b B (t • v) u i) ∈ polynomialFunctions := by
  let e : (Fin m → ℝ) →ₗ[ℝ] (L → ℝ) :=
    (coordinateOrbitSpan (polynomialModelCoordinate b)).subtype.comp B.toLinearMap
  have he : Function.Injective e := Subtype.coe_injective.comp B.injective
  apply polynomial_of_coordinateEvaluations e he
    (fun t => coordinateActionInBasis b B (t • v) u) ?_ (LinearMap.proj i)
  intro a
  have heq : (fun t : ℝ => e (coordinateActionInBasis b B (t • v) u) a) =
      (fun t => (B u : L → ℝ) (a * (t • v))) := by
    funext t
    exact coordinateActionInBasis_eval b B (t • v) u a
  rw [heq]
  exact polynomial_translated_coordinateFunction b (B u).2 a v

theorem polynomial_matrixRepresentation_entry (v : L) (i j : Fin m) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ, p.eval t =
      (polynomialMatrixRepresentation b B (t • v) : Matrix (Fin m) (Fin m) ℝ) i j :=
  mem_polynomialFunctions_iff.mp (polynomial_coordinateActionInBasis b B v (Pi.single j 1) i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPolynomialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotence of the faithful polynomial representation

The representation is polynomial on every straight one-parameter subgroup.
The actual Lie differential therefore consists of nilpotent matrices.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

theorem polynomialMatrixLieRepresentation_nilpotent (v : L) :
    IsNilpotent (polynomialMatrixLieRepresentation b B v) := by
  let A := polynomialMatrixLieRepresentation b B v
  let f : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => (polynomialMatrixRepresentation b B (t • v) : Matrix (Fin m) (Fin m) ℝ)
  have hf0 : f 0 = 1 := by
    dsimp only [f]
    rw [zero_smul, ← P.one_eq_zero, map_one]
    rfl
  have hadd (s t : ℝ) : f (s + t) = f s * f t := by
    dsimp only [f]
    rw [← PolynomialExponentialCoordinates.smul_mul (L := L) v s t, map_mul]
    rfl
  have heq : f = fun t => NormedSpace.exp (t • A) := by
    funext t
    have h := congrArg Units.val (polynomialMatrixLieRepresentation_exp b B (t • v))
    simp only [coe_algebraExpUnit, map_smul] at h
    exact h
  have hzero : HasDerivAt f A 0 := by
    rw [heq]
    let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  exact isNilpotent_of_polynomial_oneParameter hf0 hadd hzero
    (polynomial_matrixRepresentation_entry b B v)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialUnipotentModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unipotent realization of a polynomial exponential model

This construction is internal to the given polynomial model. It does not
assert the finite BCH formula for an arbitrary Lie group.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

include b in
theorem exists_polynomial_unipotent_model :
    ∃ (m c : ℕ) (ρ : L →* Matrix.GeneralLinearGroup (Fin m) ℝ)
      (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective ρ ∧ Function.Injective j ∧
      ContDiff ℝ ∞ (fun x => (ρ x : Matrix (Fin m) (Fin m) ℝ)) ∧
      (∀ x, ρ x = algebraExpUnit (j x)) ∧
      (∀ x, IsNilpotent ((ρ x : Matrix (Fin m) (Fin m) ℝ) - 1)) ∧
      (∀ l : List L, c ≤ l.length → (l.map j).prod = 0) := by
  let := finiteDimensional_polynomialModelOrbit b
  let m := Module.finrank ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b) :=
    (Module.finBasis ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))).equivFun.symm
  let j := polynomialMatrixLieRepresentation b B
  obtain ⟨c, hc⟩ := exists_vanishing_matrix_products_of_pointwise_nilpotent j
    (polynomialMatrixLieRepresentation_nilpotent b B)
  refine ⟨m, c, polynomialMatrixRepresentation b B, j,
    polynomialMatrixRepresentation_injective b B,
    polynomialMatrixLieRepresentation_injective b B,
    contDiff_polynomialMatrixRepresentation b B,
    polynomialMatrixLieRepresentation_exp b B, ?_, hc⟩
  intro x
  rw [polynomialMatrixLieRepresentation_exp, coe_algebraExpUnit]
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact isNilpotent_analytic_exp_sub_one (polynomialMatrixLieRepresentation_nilpotent b B x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateIntegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integration between polynomial exponential models

Each model has a faithful unipotent representation. Enlarging both product
bounds to their maximum gives the same universal BCH coefficients, hence
every Lie homomorphism preserves the two group laws.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L K : Type*} [RealNormedLieAlgebra L] [RealNormedLieAlgebra K]
  [FiniteDimensional ℝ L] [FiniteDimensional ℝ K]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates K]

theorem polynomialCoordinate_map_mul (f : L →ₗ⁅ℝ⁆ K) (x y : L) :
    f (x * y) = f x * f y := by
  obtain ⟨m, c, ρ, j, hρ, _, _, hexp, _, hc⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ L)
  obtain ⟨m', c', ρ', j', hρ', _, _, hexp', _, hc'⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ K)
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin m') (Fin m') ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hprod := finite_product_of_unipotent_coordinates ρ hρ j hexp (max c c')
    (fun l hl => hc l ((Nat.le_max_left c c').trans hl.le)) ![x, y]
  have hprod' := finite_product_of_unipotent_coordinates ρ' hρ' j' hexp' (max c c')
    (fun l hl => hc' l ((Nat.le_max_right c c').trans hl.le)) ![f x, f y]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at hprod hprod'
  rw [hprod, finiteDynkinPolynomial_map, hprod']
  congr 1
  funext i
  fin_cases i <;> rfl

def polynomialCoordinateHom (f : L →ₗ⁅ℝ⁆ K) : L →* K where
  toFun := f
  map_one' := by rw [P.one_eq_zero, map_zero, Q.one_eq_zero]
  map_mul' := polynomialCoordinate_map_mul f

@[simp] theorem polynomialCoordinateHom_apply (f : L →ₗ⁅ℝ⁆ K) (x : L) :
    polynomialCoordinateHom f x = f x := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntegrationToUnipotentModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating into a concretely represented nilpotent model

Both finite product formulas use a common enlarged bound. Global exponential
coordinates in the target give continuity; the exponential curves then give
smoothness and the prescribed differential.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L E G A : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem integrate_to_unipotent_model
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      j.toLinearMap.toContinuousLinearMap)
    (c : ℕ) (hc : ∀ l : List (GroupLieAlgebra (𝓘(ℝ, E)) G),
      c ≤ l.length → (l.map j).prod = 0)
    (f : L →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ φ : L →* G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, E)) ∞ φ ∧
      (∀ x, φ x = Exp (f x)) ∧
      ∀ v, mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, E)) φ 1 v = f v := by
  obtain ⟨chart, hchart⟩ := globalExponentialChart_of_finite_products Exp hExp hnil
    (universalDynkinCoefficients c)
    (fun _ X => finite_bch_of_faithful_nilpotent_representation Exp hExp ρ hρ j hd c
      (fun l hl => hc l hl.le) X)
  obtain ⟨m, d, σ, k, hσ, _, _, hσexp, _, hk⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ L)
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hmul (x y : L) : Exp (f (x * y)) = Exp (f x) * Exp (f y) := by
    have hs := finite_product_of_unipotent_coordinates σ hσ k hσexp (max d c)
      (fun l hl => hk l ((Nat.le_max_left d c).trans hl.le)) ![x, y]
    have ht := finite_bch_of_faithful_nilpotent_representation Exp hExp ρ hρ j hd (max d c)
      (fun l hl => hc l ((Nat.le_max_right d c).trans hl.le)) ![f x, f y]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at hs ht
    rw [hs, finiteDynkinPolynomial_map, ht]
    congr 2
    funext i
    fin_cases i <;> rfl
  let φ : L →* G :=
    { toFun := fun x => Exp (f x)
      map_one' := by rw [P.one_eq_zero, map_zero, hExp.map_zero]
      map_mul' := hmul }
  have hcont : Continuous φ := by
    have heq : (φ : L → G) = fun x => chart (f x) := by
      funext x
      exact (hchart _).symm
    rw [heq]
    exact chart.continuous.comp f.toLinearMap.continuous_of_finiteDimensional
  have hs := contMDiff_of_exponential_compatibility
    PolynomialExponentialCoordinates.isGroupExponential_identity hExp φ hcont
    f.toLinearMap (fun _ => rfl)
  refine ⟨φ, hs, fun _ => rfl, ?_⟩
  exact mfderiv_eq_of_exponential_compatibility
    PolynomialExponentialCoordinates.isGroupExponential_identity hExp φ
    (hs.mdifferentiable (by simp)) f.toLinearMap (fun _ => rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteProductPolynomialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exponential coordinates from a finite product law

A concrete representation may provide a polynomial law with a degree larger
than the Lie nilpotency class. That is enough for the global coordinate construction.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem polynomialExponentialCoordinates_equiv_of_finite_products
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    {c : ℕ} (coefficients : (n : ℕ) → DynkinCoefficients c n)
    (products : ∀ n (X : Fin n → GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier),
      (List.ofFn (fun i => groupExponential (X i))).prod =
        groupExponential (finiteDynkinPolynomial (coefficients n) X)) :
    ∃ P : PolynomialExponentialCoordinates L,
      ∃ e : @MulEquiv L N.carrier P.group.toMul N.group.toMul,
        ∀ x, e x = groupExponential (N.equiv x) := by
  let E := N.modelSpace
  let G := N.carrier
  let T := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : NormedAddCommGroup T := by change NormedAddCommGroup E; exact inferInstance
  let : NormedSpace ℝ T := by change NormedSpace ℝ E; exact inferInstance
  let Exp : T → G := groupExponential
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  have hn : LieRing.IsNilpotent T := N.tangent_nilpotent hnil
  obtain ⟨chart, hchart⟩ := globalExponentialChart_of_finite_products Exp hExp hn coefficients products
  let C : L ≃ₜ G := N.equiv.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hC (x : L) : C x = Exp (N.equiv x) := hchart _
  let : Group L := C.toEquiv.group
  have hmul (x y : L) : C (x * y) = C x * C y := C.apply_symm_apply _
  have hone : (1 : L) = 0 := by
    apply C.injective
    rw [show C 1 = (1 : G) from C.apply_symm_apply _]
    rw [hC, map_zero, hExp.map_zero]
  have hinv (x : L) : x⁻¹ = -x := by
    apply C.injective
    rw [show C (x⁻¹) = (C x)⁻¹ from C.apply_symm_apply _]
    rw [hC x, hC (-x), map_neg, hExp.map_neg]
  let coeff := coefficients 2
  have hprod := products 2
  have hpoly (x y : L) : x * y = finiteDynkinPolynomial coeff ![x, y] := by
    apply C.injective
    rw [hmul, hC, hC, hC]
    have he := finiteDynkinPolynomial_map N.equiv.toLieHom coeff ![x, y]
    change N.equiv (finiteDynkinPolynomial coeff ![x, y]) = _ at he
    rw [he]
    have hX : (fun i => N.equiv.toLieHom (![x, y] i)) = ![N.equiv x, N.equiv y] := by
      funext i
      fin_cases i <;> rfl
    rw [hX]
    have hp := hprod ![N.equiv x, N.equiv y]
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hp
  let : LieGroup (𝓘(ℝ, L)) ⊤ L :=
    { toIsManifold := inferInstance
      contMDiff_mul := by
        have hp : ContDiff ℝ ⊤ (fun p : L × L =>
            finiteDynkinPolynomial coeff ![p.1, p.2]) := by
          apply contDiff_normed_finiteDynkinPolynomial
          intro i
          fin_cases i
          · exact contDiff_fst
          · exact contDiff_snd
        have heq : (fun p : L × L => p.1 * p.2) =
            (fun p : L × L => finiteDynkinPolynomial coeff ![p.1, p.2]) := by
          funext p; exact hpoly _ _
        rw [heq]
        exact hp.comp_contMDiff (contMDiff_fst.prodMk_space contMDiff_snd)
      contMDiff_inv := by
        have heq : (fun x : L => x⁻¹) = fun x : L => -x := funext hinv
        rw [heq]
        exact contDiff_neg.contMDiff }
  have hidentity : IsGroupExponential (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L)) := by
    refine ⟨hone.symm, ?_, ?_⟩
    · intro v s t
      let w : L := v
      change (s + t) • w = (s • w) * (t • w)
      apply C.injective
      rw [hmul, hC, hC, hC, map_smul, map_smul, map_smul]
      exact hExp.map_add_smul _ _ _
    · intro v
      have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (show L from v)).hasMFDerivAt
      exact hd
  let φ : L →* G :=
    { C.toEquiv with
      map_one' := C.apply_symm_apply _
      map_mul' := hmul }
  have hcompat (v : L) : φ v = Exp (N.equiv v) := hC v
  have hφ := contMDiff_of_exponential_compatibility hidentity hExp φ C.continuous
    N.equiv.toLinearMap hcompat
  have hdiff (v : L) : homLieDifferential φ hφ v = N.equiv v :=
    mfderiv_eq_of_exponential_compatibility hidentity hExp φ
      (hφ.mdifferentiable (by simp)) N.equiv.toLinearMap hcompat v
  let f := N.equiv.symm.toLieHom.comp (homLieDifferential φ hφ)
  have hf (v : GroupLieAlgebra (𝓘(ℝ, L)) L) : f v = (v : L) := by
    change N.equiv.symm (homLieDifferential φ hφ v) = v
    exact (congrArg N.equiv.symm (hdiff v)).trans (N.equiv.symm_apply_apply v)
  let e := LieEquiv.ofBijective f
    ⟨fun x y h => by
      have hxy : (x : L) = (y : L) := (hf x).symm.trans (h.trans (hf y))
      exact hxy, fun y => ⟨y, hf y⟩⟩
  let P : PolynomialExponentialCoordinates L :=
          { group := inferInstance
            lieGroup := inferInstance
            one_eq_zero := hone
            inv_eq_neg := hinv
            degree := c
            coefficients := coeff
            mul_eq := hpoly
            tangentEquiv := e.symm
            tangentEquiv_apply := by
              intro x
              have he := e.apply_symm_apply x
              change f (e.symm x) = x at he
              rwa [hf] at he }
  exact ⟨P, { C.toEquiv with map_mul' := hmul }, hC⟩

/-- Forgetting the exponential chart recovers the original existence result. -/
theorem polynomialExponentialCoordinates_of_finite_products
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    {c : ℕ} (coefficients : (n : ℕ) → DynkinCoefficients c n)
    (products : ∀ n (X : Fin n → GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier),
      (List.ofFn (fun i => groupExponential (X i))).prod =
        groupExponential (finiteDynkinPolynomial (coefficients n) X)) :
    Nonempty (PolynomialExponentialCoordinates L) := by
  obtain ⟨P, _, _⟩ := polynomialExponentialCoordinates_equiv_of_finite_products
    N hnil coefficients products
  exact ⟨P⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPolynomialOperations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing the polynomial operations used in a nilpotent extension -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L V : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞ω}

theorem contDiff_binaryDynkin_comp {c : ℕ} (coeff : DynkinCoefficients c 2)
    {f g : V → L} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => finiteDynkinPolynomial coeff ![f x, g x]) := by
  apply contDiff_normed_finiteDynkinPolynomial
  intro i
  fin_cases i
  · exact hf
  · exact hg

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentSemidirectGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic semidirect products for the nilpotent induction

The carrier is the vector space `L × ℝ`. Its operations are polynomial because
the action is the exponential of a nilpotent derivation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

section Operations

theorem contDiff_derivationSemidirect_mul {r : ℕ∞ω} :
    ContDiff ℝ r (fun p : (L × ℝ) × (L × ℝ) =>
      (finiteDynkinPolynomial P.coefficients
        ![p.1.1, nilpotentDerivationFlow D hD p.1.2 p.2.1], p.1.2 + p.2.2)) := by
  have hflow : ContDiff ℝ r (fun p : (L × ℝ) × (L × ℝ) =>
      nilpotentDerivationFlow D hD p.1.2 p.2.1) :=
    contDiff_derivationFlow_comp D hD (contDiff_fst.snd) (contDiff_snd.fst)
  have hpoly : ContDiff ℝ r (fun p : (L × ℝ) × (L × ℝ) =>
      finiteDynkinPolynomial P.coefficients ![p.1.1, nilpotentDerivationFlow D hD p.1.2 p.2.1]) := by
    exact contDiff_binaryDynkin_comp P.coefficients (contDiff_fst.fst) hflow
  exact hpoly.prodMk ((contDiff_fst.snd).add (contDiff_snd.snd))

theorem derivationSemidirectLieGroup :
    letI := derivationSemidirectGroup D hD
    LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ) := by
  let := derivationSemidirectGroup D hD
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have heq : (fun p : (L × ℝ) × (L × ℝ) => (derivationSemidirectGroup D hD).mul p.1 p.2) =
        (fun p => (finiteDynkinPolynomial P.coefficients
          ![p.1.1, nilpotentDerivationFlow D hD p.1.2 p.2.1], p.1.2 + p.2.2)) := by
      funext p
      rw [derivationSemidirect_mul, P.mul_eq]
    change ContMDiff _ _ _ (fun p : (L × ℝ) × (L × ℝ) =>
      (derivationSemidirectGroup D hD).mul p.1 p.2)
    rw [heq]
    exact (contDiff_derivationSemidirect_mul D hD).comp_contMDiff
      (contMDiff_fst.prodMk_space contMDiff_snd)
  · have heq : (fun p : L × ℝ => (derivationSemidirectGroup D hD).inv p) =
        (fun p => (nilpotentDerivationFlow D hD (-p.2) (-p.1), -p.2)) :=
      funext (derivationSemidirect_inv D hD)
    change ContMDiff _ _ _ (fun p : L × ℝ => (derivationSemidirectGroup D hD).inv p)
    rw [heq]
    exact (contDiff_derivationSemidirect_inv D hD).contMDiff

end Operations
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentCodimensionOneModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a polynomial ideal model by one dimension -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [LieRing.IsNilpotent L] (C : LieCodimensionOneData L)

set_option backward.isDefEq.respectTransparency false in
def nilpotentModelOfPolynomialIdeal
    (P : letI := C.normedIdeal; PolynomialExponentialCoordinates C.ideal) :
    NilpotentLieModel L := by
  letI := C.normedIdeal
  letI := P
  let D := C.derivation
  have hD : IsNilpotent D.toLinearMap := C.derivation_nilpotent
  let normedV : NormedAddCommGroup (C.ideal × ℝ) := inferInstance
  letI : NormedAddCommGroup (C.ideal × ℝ) := normedV
  letI : AddCommGroup (C.ideal × ℝ) := normedV.toAddCommGroup
  letI : MetricSpace (C.ideal × ℝ) := normedV.toMetricSpace
  letI : UniformSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  letI : TopologicalSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : ChartedSpace (C.ideal × ℝ) (C.ideal × ℝ) := chartedSpaceSelf _
  letI : T0Space (C.ideal × ℝ) := @MetricSpace.instT0Space _ normedV.toMetricSpace
  letI : T2Space (C.ideal × ℝ) := inferInstance
  letI : CompleteSpace (C.ideal × ℝ) := FiniteDimensional.complete ℝ (C.ideal × ℝ)
  letI : Group (C.ideal × ℝ) := derivationSemidirectGroup D hD
  letI : LieGroup (𝓘(ℝ, C.ideal × ℝ)) ⊤ (C.ideal × ℝ) := derivationSemidirectLieGroup D hD
  letI : LieRing (C.ideal × ℝ) :=
    inferInstanceAs (LieRing (GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ)))
  letI : LieAlgebra ℝ (C.ideal × ℝ) :=
    inferInstanceAs (LieAlgebra ℝ (GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ)))
  letI : MeasurableSpace (C.ideal × ℝ) := borel (C.ideal × ℝ)
  letI : BorelSpace (C.ideal × ℝ) := ⟨rfl⟩
  have hbr (x y : C.ideal) (s t : ℝ) :
      ⁅((x, s) : GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ)),
        ((y, t) : GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ))⁆ =
      (⁅x, y⁆ + s • D y - t • D x, 0) :=
    semidirect_tangent_bracket D hD (derivationSemidirect_one D hD)
      (derivationSemidirect_mul D hD) x y s t
  let e : GroupLieAlgebra (𝓘(ℝ, C.ideal × ℝ)) (C.ideal × ℝ) ≃ₗ⁅ℝ⁆ L :=
    { C.split with
      map_lie' := by
        intro x y
        let xp : C.ideal × ℝ := x
        let yp : C.ideal × ℝ := y
        have hh := hbr xp.1 yp.1 xp.2 yp.2
        exact (congrArg C.split hh).trans (C.split_lie xp.1 yp.1 xp.2 yp.2).symm }
  exact { modelSpace := C.ideal × ℝ, carrier := C.ideal × ℝ, equiv := e.symm }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectAxisExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential curves along the two factors of the semidirect product -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem semidirect_exp_left_axis (x : L) (t : ℝ) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    groupExponential (G := L × ℝ) (t • ((x, 0) : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) =
      (t • x, 0) := by
  let _ : Group (L × ℝ) := derivationSemidirectGroup D hD
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  let v : L × ℝ := (x, 0)
  have hzero : (0 : ℝ) • v = (1 : L × ℝ) := by
    rw [zero_smul]
    exact (derivationSemidirect_one D hD).symm
  have hmul (s u : ℝ) : (s + u) • v = (s • v) * (u • v) := by
    change (s + u) • v = (derivationSemidirectGroup D hD).mul (s • v) (u • v)
    rw [derivationSemidirect_mul]
    simp only [v, Prod.smul_mk, smul_zero, nilpotentDerivationFlow_zero,
      PolynomialExponentialCoordinates.smul_mul, zero_add]
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v).hasMFDerivAt
  have h := oneParameter_eq_groupExponential groupExponential_isGroupExponential hzero hmul v hd t
  have hv : t • v = (t • x, 0) := by simp [v]
  exact h.symm.trans hv

theorem semidirect_exp_right_axis (t : ℝ) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    groupExponential (G := L × ℝ) (t • ((0, 1) : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) =
      (0, t) := by
  let _ : Group (L × ℝ) := derivationSemidirectGroup D hD
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  let v : L × ℝ := (0, 1)
  have hzero : (0 : ℝ) • v = (1 : L × ℝ) := by
    rw [zero_smul]
    exact (derivationSemidirect_one D hD).symm
  have hmul (s u : ℝ) : (s + u) • v = (s • v) * (u • v) := by
    change ((s + u) • (0 : L), (s + u) * 1) =
      (s • (0 : L) * nilpotentDerivationFlow D hD (s * 1) (u • (0 : L)), s * 1 + u * 1)
    simp only [smul_zero, mul_one, map_zero]
    rw [← P.one_eq_zero, mul_one]
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v).hasMFDerivAt
  have h := oneParameter_eq_groupExponential groupExponential_isGroupExponential hzero hmul v hd t
  have hv : t • v = (0, t) := by simp [v]
  exact h.symm.trans hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectUnipotentRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Faithful unipotent representation of the semidirect model

Only the smaller ideal has polynomial exponential coordinates. For the new
model, polynomial coordinate translates and the two factor subgroups suffice.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

include b in
theorem semidirectMatrixProducts
    (hnil : letI := derivationSemidirectGroup D hD
      letI := derivationSemidirectLieGroup D hD
      LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    ∀ {m : ℕ} (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b)),
    ∃ c : ℕ, ∀ l : List (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)),
      c ≤ l.length →
        (l.map (coordinateMatrixDifferential (semidirectCoordinate b) B
          (contDiff_semidirectCoordinate b))).prod = 0 := by
  let := derivationSemidirectGroup D hD
  let _ : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  intro m B
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let _ : LieRing.IsNilpotent T := hnil
  let q := semidirectCoordinate b
  have hq : ∀ i, ContDiff ℝ ∞ (q i) := contDiff_semidirectCoordinate b
  let j := coordinateMatrixDifferential q B hq
  let S : Set T := Set.range (fun x : L => ((x, 0) : T)) ∪ {((0, 1) : T)}
  have hS : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    intro v _
    let p : L × ℝ := v
    have hleft : ((p.1, 0) : T) ∈ Submodule.span ℝ S :=
      Submodule.subset_span (Or.inl ⟨p.1, rfl⟩)
    have hright : ((0, 1) : T) ∈ Submodule.span ℝ S :=
      Submodule.subset_span (Or.inr (Set.mem_singleton _))
    have hsum := (Submodule.span ℝ S).add_mem hleft
      ((Submodule.span ℝ S).smul_mem p.2 hright)
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    change p = ((p.1, 0) : L × ℝ) + p.2 • ((0, 1) : L × ℝ)
    ext <;> simp
  have hj (v : T) (hv : v ∈ S) : IsNilpotent (j v) := by
    rcases hv with ⟨x, rfl⟩ | hv
    · apply coordinateMatrixDifferential_nilpotent q B hq
      intro a z i
      have he (t : ℝ) : groupExponential (t • ((x, 0) : T)) =
          t • ((x, 0) : L × ℝ) := by
        exact (semidirect_exp_left_axis D hD x t).trans (by simp)
      have heq : (fun t : ℝ => q i (a * groupExponential (t • ((x, 0) : T)) * z)) =
          (fun t : ℝ => q i (a * (t • ((x, 0) : L × ℝ)) * z)) :=
        funext fun t => congrArg (fun p : L × ℝ => q i (a * p * z)) (he t)
      exact heq.symm ▸ semidirect_translated_line_polynomial b D hD a (x, 0) z i
    · obtain rfl := Set.mem_singleton_iff.mp hv
      apply coordinateMatrixDifferential_nilpotent q B hq
      intro a z i
      have he (t : ℝ) : groupExponential (t • ((0, 1) : T)) =
          t • ((0, 1) : L × ℝ) := by
        exact (semidirect_exp_right_axis D hD t).trans (by simp)
      have heq : (fun t : ℝ => q i (a * groupExponential (t • ((0, 1) : T)) * z)) =
          (fun t : ℝ => q i (a * (t • ((0, 1) : L × ℝ)) * z)) :=
        funext fun t => congrArg (fun p : L × ℝ => q i (a * p * z)) (he t)
      exact heq.symm ▸ semidirect_translated_line_polynomial b D hD a (0, 1) z i
  obtain ⟨c, hc⟩ := matrix_products_vanish_of_spanning_nilpotents j S hS hj
  exact ⟨c, hc⟩

include b in
theorem exists_semidirect_unipotent_representation
    (hnil : letI := derivationSemidirectGroup D hD
      letI := derivationSemidirectLieGroup D hD
      LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) :
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    letI : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
    letI := derivationSemidirectLieGroup D hD
    ∃ (m c : ℕ) (ρ : (L × ℝ) →* Matrix.GeneralLinearGroup (Fin m) ℝ)
      (j : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective ρ ∧ Function.Injective j ∧
      @HasMFDerivAt ℝ _ (L × ℝ) _ _ (L × ℝ) _ (𝓘(ℝ, L × ℝ))
        (L × ℝ) _ _ (Matrix (Fin m) (Fin m) ℝ) _ _
        (Matrix (Fin m) (Fin m) ℝ) _ (𝓘(ℝ, Matrix (Fin m) (Fin m) ℝ))
        (Matrix (Fin m) (Fin m) ℝ) _ (chartedSpaceSelf _)
        (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) 1 j.toLinearMap.toContinuousLinearMap ∧
      (∀ l : List (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)),
        c ≤ l.length → (l.map j).prod = 0) := by
  let := derivationSemidirectGroup D hD
  let _ : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let _ : LieRing.IsNilpotent T := hnil
  let q := semidirectCoordinate b
  let := finiteDimensional_semidirectCoordinateOrbit b D hD
  let m := Module.finrank ℝ (coordinateOrbitSpan q)
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q :=
    (Module.finBasis ℝ (coordinateOrbitSpan q)).equivFun.symm
  have hq : ∀ i, ContDiff ℝ ∞ (q i) := contDiff_semidirectCoordinate b
  let ρ := coordinateMatrixRepresentation q B
  let j := coordinateMatrixDifferential q B hq
  obtain ⟨c, hc⟩ := semidirectMatrixProducts b D hD hnil B
  exact ⟨m, c, ρ, j,
    coordinateMatrixRepresentation_injective q B (semidirectCoordinate_injective b),
    coordinateMatrixDifferential_injective q B hq (semidirectCoordinate_injective b),
    hasMFDerivAt_unitsHomLieDifferential ρ (contDiff_coordinateMatrixRepresentation q B hq).contMDiff,
    hc⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialIdealExtensionCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending polynomial exponential coordinates by one dimension

The smaller ideal supplies its polynomial coordinates. The new semidirect
model is represented directly from coordinate translates, so no BCH formula
on the new model is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [LieRing.IsNilpotent L] (C : LieCodimensionOneData L)

set_option backward.isDefEq.respectTransparency false in
theorem polynomialCoordinates_extend_ideal
    (P : letI := C.normedIdeal; PolynomialExponentialCoordinates C.ideal) :
    Nonempty (PolynomialExponentialCoordinates L) := by
  let := C.normedIdeal
  let := P
  let D := C.derivation
  have hD : IsNilpotent D.toLinearMap := C.derivation_nilpotent
  let normedV : NormedAddCommGroup (C.ideal × ℝ) := inferInstance
  let : NormedAddCommGroup (C.ideal × ℝ) := normedV
  let : AddCommGroup (C.ideal × ℝ) := normedV.toAddCommGroup
  let : MetricSpace (C.ideal × ℝ) := normedV.toMetricSpace
  let : UniformSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  let : TopologicalSpace (C.ideal × ℝ) :=
    normedV.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : ChartedSpace (C.ideal × ℝ) (C.ideal × ℝ) := chartedSpaceSelf _
  let : T0Space (C.ideal × ℝ) := @MetricSpace.instT0Space _ normedV.toMetricSpace
  let : T2Space (C.ideal × ℝ) := inferInstance
  let : CompleteSpace (C.ideal × ℝ) := FiniteDimensional.complete ℝ (C.ideal × ℝ)
  let N := nilpotentModelOfPolynomialIdeal C P
  let _ : Group (C.ideal × ℝ) := derivationSemidirectGroup D hD
  let _ : LieGroup (𝓘(ℝ, C.ideal × ℝ)) ⊤ (C.ideal × ℝ) := derivationSemidirectLieGroup D hD
  have hn := N.tangent_nilpotent (inferInstance : LieRing.IsNilpotent L)
  obtain ⟨m, c, ρ, j, hρ, _, hd, hc⟩ := exists_semidirect_unipotent_representation
    (Module.finBasis ℝ C.ideal) D hD hn
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply polynomialExponentialCoordinates_of_finite_products N
    (inferInstance : LieRing.IsNilpotent L) (universalDynkinCoefficients c)
  intro n X
  exact finite_bch_of_faithful_nilpotent_representation groupExponential
    groupExponential_isGroupExponential ρ hρ j hd c (fun l hl => hc l hl.le) X

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelDynkin
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise finite BCH input for polynomial coordinate models

The faithful representation gives a finite product formula at a concrete
operator bound. Coefficient stability and vanishing of long brackets reduce
it to every supplied lower-central-series bound.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialCoordinate_product_of_class {c n : ℕ}
    (hc : LieModule.lowerCentralSeries ℝ L L c = ⊥) (X : Fin n → L) :
    (List.ofFn X).prod = finiteDynkinPolynomial (universalDynkinCoefficients c n) X := by
  obtain ⟨m, d, ρ, j, hρ, _, _, hexp, _, hd⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ L)
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hp := finite_product_of_unipotent_coordinates ρ hρ j hexp (max c d)
    (fun l hl => hd l ((Nat.le_max_right c d).trans hl.le)) X
  exact hp.trans (universalDynkinPolynomial_truncate (Nat.le_max_left c d) hc X)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPublishedInputs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent published-input family used by the Cartan construction

The finite BCH expansion follows Baudoin (2004), Appendix B.5--B.6.
The intrinsic adjoint calculation and integration into arbitrary Lie groups
give model existence, global coordinates, integration, and exponential
Haar compatibility.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

/-- Finite BCH and simple connectedness give the global exponential chart. -/
theorem NilpotentPublishedInputs.coordinates (h : NilpotentPublishedInputs)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) : NilpotentGlobalExponentialChartInput N.modelSpace N.carrier :=
  nilpotentGlobalExponentialChart_of_dynkin (h.dynkin L N)

/-- Global integral curves give the exponential, and the BCH Jacobian gives
the Haar compatibility of every exponential basis chart. -/
theorem NilpotentPublishedInputs.haar (h : NilpotentPublishedInputs)
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) : NilpotentExponentialHaarInput N.modelSpace N.carrier :=
  ((h.coordinates L N).toCoordinates (h.dynkin L N)).toHaar

/-- The nilpotent-target specialization is constructed from exponential
coordinates and the common BCH identity on the product group. -/
theorem NilpotentPublishedInputs.integrate (h : NilpotentPublishedInputs)
    (L K : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [LieRing K] [LieAlgebra ℝ K] [FiniteDimensional ℝ K] [LieRing.IsNilpotent K]
    (N : NilpotentLieModel L) (Q : NilpotentLieModel K) :
    NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier)
      (EG := Q.modelSpace) (G := Q.carrier) :=
  nilpotentLieIntegrationInput_of_smooth
    (nilpotentSmoothIntegration_of_coordinates (h.coordinates L N) (h.coordinates K Q)
      h.dynkin (Q.tangent_nilpotent inferInstance))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorLocalChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth local coordinates from the complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

def cartanParameter : E →L[ℝ] F.D.modelSpace :=
  (show E →ₗ[ℝ] F.D.modelSpace from
    F.D.equiv.toLinearMap.comp (T.cartanComponent H)).toContinuousLinearMap

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteSemisimpleLiftFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # A finite commuting semisimple family adapted to quotient generators

Successive inner corrections preserve the earlier semisimple factors. Every
member of a finite list in the abelian quotient therefore has a lift in one
common centralizer, with its semisimple factor belonging to that family.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

def HasSemisimpleLift (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (ss : List (L ≃ₗ⁅ℝ⁆ L)) (q : Q) : Prop :=
  ∃ g : G, g ∈ commonSemisimpleCentralizer E ss ∧ E.rightHom g = q ∧
    ∃ S ∈ ss, ∃ U : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (U.toLinearMap - 1) ∧
      Commute S.toLinearMap U.toLinearMap ∧
      (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearMap =
        S.toLinearMap * U.toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedSubalgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint fixed algebra and its unipotent quotient-lift actions -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def jointFixedLieSubalgebra (ss : List (L ≃ₗ⁅ℝ⁆ L)) : LieSubalgebra ℝ L where
  toSubmodule :=
    { carrier := {x | ∀ S ∈ ss, S x = x}
      zero_mem' := by intro S _; exact map_zero S
      add_mem' := by
        intro x y hx hy S hS
        rw [map_add, hx S hS, hy S hS]
      smul_mem' := by
        intro r x hx S hS
        rw [map_smul, hx S hS] }
  lie_mem' := by
    intro x y hx hy S hS
    rw [S.map_lie, hx S hS, hy S hS]

omit [FiniteDimensional ℝ L] in
theorem mem_jointFixedLieSubalgebra (ss : List (L ≃ₗ⁅ℝ⁆ L)) (x : L) :
    x ∈ jointFixedLieSubalgebra ss ↔ ∀ S ∈ ss, S x = x := Iff.rfl

end PolycyclicRecognition

end

end OAI
end


