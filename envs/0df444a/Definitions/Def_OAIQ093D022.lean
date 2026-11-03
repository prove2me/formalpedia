-- Prove2me | Definitions.Def_OAIQ093D022
-- name    : OAIQ093D022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:38:32.953339+00:00
-- url     : https://prove2.me/theorems/8e46dd78-6562-4c67-b1e5-deaf5b640837
-- title:
--   Definitions bundle OAIQ093D022 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 9 definitions, 1 inductive type or structure and 15 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.LinkedSource`, `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryComparison`, `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryModel`, `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryModel.sectionMap`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceCell`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.SmoothRotationalModification`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.factorCompactRotationAction`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.smoothRotationalModificationChartedSpace`, `OAI.PolycyclicRecognition.nilradicalRotations`, `OAI.PolycyclicRecognition.shadowKernelParameter`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_ConstructedNilpotentPublishedInputs`, `PolycyclicRecognition_Algebra_IntrinsicGroupDynkin`, `PolycyclicRecognition_Algebra_NilpotentAutomorphismAction`, `PolycyclicRecognition_Algebra_NilpotentIntrinsicIntegration`, `PolycyclicRecognition_Algebra_NilpotentModelIntegration`, `PolycyclicRecognition_Geometry_ActualSmoothRotation`, `PolycyclicRecognition_Geometry_CartanPolarSourceFrames`, `PolycyclicRecognition_Geometry_CartanRayBoundaryComparison`, `PolycyclicRecognition_Geometry_CartanRayBoundaryModel`, `PolycyclicRecognition_Geometry_CartanTiledSourceCell`, `PolycyclicRecognition_Geometry_FactorRotationCharacter`, `PolycyclicRecognition_Geometry_IntegratedCartanRotations`, `PolycyclicRecognition_Geometry_IntegratedNilradicalRotations`, `PolycyclicRecognition_Geometry_ShadowExponentialCoordinates`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D027` and `OAIQ093D020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ093D023`; the statements `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.nonempty_linkedSource_of_exp`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryModel.contracts_compact_orbits`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_first`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints`, `OAI.PolycyclicRecognition.CartanWordModel.exists_ray_boundary_family_homeomorphisms`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge`, `OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_affine_bound_of_boundary_comparisons`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_transversal_traces_of_boundary_comparisons` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model`; the proofs of `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.nonempty_linkedSource_of_exp`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_box_law_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.RayBoundaryModel.contracts_compact_orbits`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_first`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints`, `OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.exists_ray_boundary_family_homeomorphisms`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_height_intrinsic`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.nonempty_rayBoundaryComparison_of_shadows`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_affine_bound_of_boundary_comparisons`, `OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_published_inputs_and_sublinear`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_transversal_traces_of_boundary_comparisons`, `OAI.PolycyclicRecognition.NilpotentLieModel.group_nilpotent`, `OAI.PolycyclicRecognition.cartan_cover_controlled_pairs`, `OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing`, `OAI.PolycyclicRecognition.exists_intrinsic_smooth_coordinates`, `OAI.PolycyclicRecognition.exists_triangulable_model_of_representations`, `OAI.PolycyclicRecognition.exponentialLinearRealizationInput_intrinsic`, `OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff`, `OAI.PolycyclicRecognition.intrinsic_exponential_injective`, `OAI.PolycyclicRecognition.isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel`, `OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice`, `OAI.PolycyclicRecognition.polynomialBoundedChainPacking_intrinsic` and `OAI.PolycyclicRecognition.trace_ad_eq_zero_of_intrinsic_kernel_haar`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentIntrinsicIntegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent-source integration into any Lie group

Codimension-one induction uses the intrinsic adjoint exponential identity.
The target has no representation hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

set_option backward.isDefEq.respectTransparency false in
theorem integrate_polynomial_nilpotent
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
    [P : PolynomialExponentialCoordinates L] (hnil : LieRing.IsNilpotent L)
    (f : L →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ φ : L →* G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, E)) ∞ φ ∧
      ∀ x, φ x = Exp (f x) := by
  have hmain : ∀ n : ℕ, ∀ (V : Type) [RealNormedLieAlgebra V] [FiniteDimensional ℝ V]
      [PV : PolynomialExponentialCoordinates V], Module.finrank ℝ V = n →
      LieRing.IsNilpotent V → ∀ f : V →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G,
      ∃ φ : V →* G, ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ φ ∧ ∀ x, φ x = Exp (f x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ PV hv hV f
      let : LieRing.IsNilpotent V := hV
      by_cases hs : Subsingleton V
      · let := hs
        refine ⟨1, contMDiff_const, ?_⟩
        intro x
        have hx : x = 0 := Subsingleton.elim _ _
        simp only [hx, map_zero, hExp.map_zero, MonoidHom.one_apply]
      · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨C⟩ := exists_nilpotentCodimensionOneData (L := V)
        let := C.normedIdeal
        let normedI : NormedAddCommGroup C.ideal := inferInstance
        let : NormedAddCommGroup C.ideal := normedI
        let : AddCommGroup C.ideal := normedI.toAddCommGroup
        let : MetricSpace C.ideal := normedI.toMetricSpace
        let : UniformSpace C.ideal :=
          normedI.toMetricSpace.toPseudoMetricSpace.toUniformSpace
        let : TopologicalSpace C.ideal :=
          normedI.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        let : IsTopologicalAddGroup C.ideal := inferInstance
        let : ChartedSpace C.ideal C.ideal := chartedSpaceSelf _
        have hI : LieRing.IsNilpotent C.ideal := C.ideal_nilpotent
        obtain ⟨PI⟩ := polynomialExponentialCoordinates_nilpotent C.ideal hI
        let := PI
        have hdim : Module.finrank ℝ C.ideal < n := hv ▸ C.finrank_ideal_lt
        let fi : C.ideal →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G :=
          f.comp C.ideal.incl
        obtain ⟨k, hk, hkexp⟩ := ih (Module.finrank ℝ C.ideal) hdim C.ideal rfl hI fi
        let D := C.derivation
        have hD : IsNilpotent D.toLinearMap := C.derivation_nilpotent
        have hinter (x : C.ideal) : fi (D x) = ⁅f C.unit, fi x⁆ := by
          change f ⁅C.unit, (x : V)⁆ = ⁅f C.unit, f (x : V)⁆
          exact f.map_lie _ _
        have hact (t : ℝ) (x : C.ideal) : k (nilpotentDerivationFlow D hD t x) =
            Exp (t • f C.unit) * k x * (Exp (t • f C.unit))⁻¹ := by
          rw [hkexp, hkexp]
          exact derivationFlow_intrinsic_conjugation D hD Exp hExp
            fi.toLinearMap (f C.unit) hinter t x
        let S := C.ideal × ℝ
        let normedS : NormedAddCommGroup S := by
          change NormedAddCommGroup (C.ideal × ℝ)
          infer_instance
        let : NormedAddCommGroup S := normedS
        let : AddCommGroup S := normedS.toAddCommGroup
        let : MetricSpace S := normedS.toMetricSpace
        let : UniformSpace S := normedS.toMetricSpace.toPseudoMetricSpace.toUniformSpace
        let : TopologicalSpace S :=
          normedS.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        let : ChartedSpace S S := chartedSpaceSelf _
        let : T0Space S := @MetricSpace.instT0Space S normedS.toMetricSpace
        let : T2Space S := inferInstance
        let : CompleteSpace S := FiniteDimensional.complete ℝ S
        let : Group S := derivationSemidirectGroup D hD
        let : MulOneClass S := (derivationSemidirectGroup D hD).toMulOneClass
        let : Mul S := (derivationSemidirectGroup D hD).toMul
        let : One S := (derivationSemidirectGroup D hD).toOne
        let : LieGroup (𝓘(ℝ, S)) ⊤ S := derivationSemidirectLieGroup D hD
        let N := nilpotentModelOfPolynomialIdeal C PI
        have hnS : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, S)) S) :=
          N.tangent_nilpotent hV
        let ψ : S →* G := derivationSemidirectHom D hD Exp hExp k (f C.unit) hact
        have hψ : ContMDiff (𝓘(ℝ, S)) (𝓘(ℝ, E)) ∞ ψ :=
          contMDiff_derivationSemidirectHom D hD Exp hExp k (f C.unit) hact hk
        have dk : HasMFDerivAt (𝓘(ℝ, C.ideal)) (𝓘(ℝ, E)) k 1
            fi.toLinearMap.toContinuousLinearMap := by
          apply (hk.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
          ext x
          exact mfderiv_eq_of_exponential_compatibility
            PolynomialExponentialCoordinates.isGroupExponential_identity hExp k
            (hk.mdifferentiable (by simp)) fi.toLinearMap hkexp x
        have hdψ := hasMFDerivAt_derivationSemidirectHom D hD Exp hExp k (f C.unit) hact
          fi.toLinearMap.toContinuousLinearMap dk
        have hψder (v : GroupLieAlgebra (𝓘(ℝ, S)) S) :
            mfderiv (𝓘(ℝ, S)) (𝓘(ℝ, E)) ψ 1 v = f (C.split v) := by
          have hone : (1 : S) = 0 := derivationSemidirect_one D hD
          rw [hone, hdψ.mfderiv]
          change f (v.1 : V) + v.2 • f C.unit = f ((v.1 : V) + v.2 • C.unit)
          rw [map_add, map_smul]
        obtain ⟨m, c, σ, q, hσ, _, dq, hc⟩ :=
          exists_semidirect_unipotent_representation (Module.finBasis ℝ C.ideal) D hD hnS
        let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
        obtain ⟨η, hη, hηexp, _⟩ := integrate_to_unipotent_model
          groupExponential groupExponential_isGroupExponential hnS σ hσ q dq c hc N.equiv.toLieHom
        let φ : V →* G := ψ.comp η
        refine ⟨φ, hψ.comp hη, ?_⟩
        intro x
        change ψ (η x) = Exp (f x)
        rw [hηexp]
        have he := groupExponential_isGroupExponential.map_of_mdifferentiable
          hExp ψ (hψ.mdifferentiable (by simp)) (N.equiv x)
        erw [hψder] at he
        exact he.trans (congrArg (fun z => Exp (f z)) (C.split.apply_symm_apply x))
  exact hmain (Module.finrank ℝ L) L rfl hnil f

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_IntrinsicGroupDynkin
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite BCH for arbitrary finite-dimensional real Lie groups

The constructed nilpotent coordinate model maps to the target by the proved
intrinsic integration theorem. Its exact class-bounded product formula descends
without a representation or simple-connectivity hypothesis on the target.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem nilpotentDynkinExpansionInput : NilpotentDynkinExpansionInput E G := by
  intro Exp hExp c hc n
  let T := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : RealNormedLieAlgebra T :=
    { (inferInstance : NormedAddCommGroup E), (inferInstance : LieRing T),
      (inferInstance : NormedSpace ℝ E), (inferInstance : LieAlgebra ℝ T) with }
  let finiteT : FiniteDimensional ℝ T := by
    change FiniteDimensional ℝ E
    infer_instance
  have hn : LieRing.IsNilpotent T := (LieModule.isNilpotent_iff ℝ T T).mpr ⟨c, hc⟩
  obtain ⟨P⟩ := @polynomialExponentialCoordinates_nilpotent T _ finiteT hn
  let := P
  let : Group T := P.group
  obtain ⟨φ, _, hφ⟩ := @integrate_polynomial_nilpotent E G _ _ _ _ _ _ _ _ Exp hExp T _ finiteT P hn (LieHom.id)
  refine ⟨universalDynkinCoefficients c n, universalDynkinCoefficients_bound c n, ?_⟩
  intro X
  have hp := congrArg φ (@polynomialCoordinate_product_of_class T _ finiteT P c n hc X)
  rw [map_list_prod, List.map_ofFn] at hp
  simp only [Function.comp_def, hφ] at hp
  convert hp using 1 <;> rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConstructedNilpotentPublishedInputs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the nilpotent published-input family

The finite BCH formula holds for every nilpotent Lie model. Together
with the model construction, global chart, integration, and Haar identities,
this proves the nilpotent input record without additional hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition

/-- The nilpotent BCH expansion holds without additional hypotheses. -/
theorem nilpotentPublishedInputs : NilpotentPublishedInputs where
  dynkin := fun _ _ _ _ _ => nilpotentDynkinExpansionInput

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentModelIntegration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a given nilpotent model into any Lie group

The now-proved nilpotent-model comparison transports the source to the
constructed coordinate model. Intrinsic integration then reaches the target.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem nilpotentSmoothIntegrationInput
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) :
    NilpotentSmoothIntegrationInput (EN := N.modelSpace) (N := N.carrier) (EG := E) (G := G) := by
  intro _ hn f
  let b := Module.finBasis ℝ L
  let : NormedAddCommGroup L := NormedAddCommGroup.induced L _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ L := NormedSpace.induced ℝ L _ b.equivFun
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  have hL : LieRing.IsNilpotent L := N.equiv.nilpotent_iff_equiv_nilpotent.mpr hn
  let : LieRing.IsNilpotent L := hL
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hL
  let := P
  let : Group L := P.group
  let Q := polynomialCoordinateLieModel L
  let fL := f.comp N.equiv.toLieHom
  obtain ⟨φ, hφ, hφexp⟩ := integrate_polynomial_nilpotent
    groupExponential groupExponential_isGroupExponential L hL fL
  obtain ⟨η, hη, _, hηexp⟩ := nilpotentPublishedInputs.integrate L L N Q inferInstance hn
    (Q.equiv.toLieHom.comp N.equiv.symm.toLieHom) groupExponential
    (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L))
    groupExponential_isGroupExponential
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := L) (P := P))
  change N.carrier →* L at η
  change ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, L)) ∞ η at hη
  change ∀ v : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier,
    η (groupExponential v) = P.tangentEquiv (N.equiv.symm v) at hηexp
  let χ : N.carrier →* G := φ.comp η
  have hχ := hφ.comp hη
  have hχexp (v : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
      χ (groupExponential v) = groupExponential (f v) := by
    change φ (η (groupExponential v)) = _
    rw [hηexp]
    rw [P.tangentEquiv_apply, hφexp]
    change groupExponential (f (N.equiv (N.equiv.symm v))) = _
    rw [N.equiv.apply_symm_apply]
  exact ⟨χ, hχ, mfderiv_eq_of_exponential_compatibility
    groupExponential_isGroupExponential groupExponential_isGroupExponential
    χ (hχ.mdifferentiable (by simp)) f.toLinearMap hχexp⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAutomorphismAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a continuous action on a nilpotent Lie algebra

The group laws follow by checking the global exponential coordinates. Those
same coordinates give joint continuity, rather than merely continuity of each
automorphism separately.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L K : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group K] [TopologicalSpace K]

theorem exists_nilpotent_automorphism_action
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp)
    (ρ : K →* (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₗ[ℝ]
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier))
    (hρlie : ∀ k x y, ρ k ⁅x, y⁆ = ⁅ρ k x, ρ k y⁆)
    (hρcont : Continuous (fun p : K × GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier =>
      ρ p.1 p.2)) :
    ∃ α : K →* MulAut N.carrier,
      Continuous (fun p : K × N.carrier => α p.1 p.2) ∧
      (∀ k x, α k (Exp x) = Exp (ρ k x)) ∧
      ∀ k, ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ (α k) := by
  obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar L N).2 Exp hExp
    (N.tangent_nilpotent hnil)).1
  have hex (k : K) : ∃ f : N.carrier →* N.carrier,
      ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ f ∧
      ∀ x, f (Exp x) = Exp (ρ k x) := by
    let j : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier →ₗ⁅ℝ⁆
        GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier :=
      { __ := (ρ k).toLinearMap
        map_lie' := fun {x y} => hρlie k x y }
    obtain ⟨f, hf, _, he⟩ := nilpotentLieIntegrationInput_of_smooth
      (nilpotentSmoothIntegrationInput L N) inferInstance (N.tangent_nilpotent hnil)
      j Exp Exp hExp hExp
    exact ⟨f, hf, he⟩
  choose F hFsmooth hFexp using hex
  have hFone (x : N.carrier) : F 1 x = x := by
    obtain ⟨v, hv⟩ := c.surjective x
    rw [hc] at hv
    rw [← hv, hFexp, map_one]
    rfl
  have hFmul (k l : K) (x : N.carrier) : F (k * l) x = F k (F l x) := by
    obtain ⟨v, hv⟩ := c.surjective x
    rw [hc] at hv
    rw [← hv, hFexp, hFexp, hFexp, map_mul]
    rfl
  let a (k : K) : MulAut N.carrier :=
    { toFun := F k
      invFun := F k⁻¹
      left_inv := fun x => by rw [← hFmul, inv_mul_cancel, hFone]
      right_inv := fun x => by rw [← hFmul, mul_inv_cancel, hFone]
      map_mul' := (F k).map_mul }
  let α : K →* MulAut N.carrier :=
    { toFun := a
      map_one' := by ext x; exact hFone x
      map_mul' := by intro k l; ext x; exact hFmul k l x }
  refine ⟨α, ?_, hFexp, hFsmooth⟩
  change Continuous (fun p : K × N.carrier => F p.1 p.2)
  have he : (fun p : K × N.carrier => F p.1 p.2) =
      (fun p => c (ρ p.1 (c.symm p.2))) := by
    funext p
    have h := hFexp p.1 (c.symm p.2)
    rw [← hc, c.apply_symm_apply, ← hc] at h
    exact h
  rw [he]
  exact c.continuous.comp (hρcont.comp
    (continuous_fst.prodMk (c.symm.continuous.comp continuous_snd)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntegratedNilradicalRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotations on the closed nilpotent factor -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (N : NilpotentLieModel T.kernelIdeal)

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

attribute [local instance] OAI.PolycyclicRecognition.modelKernelTopologicalAddGroup
theorem exists_integrated_nilradical_rotations
    (Exp : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) :
    ∃ α : realRotationTorus L H →* MulAut N.carrier,
      Continuous (fun p : realRotationTorus L H × N.carrier => α p.1 p.2) ∧
      (∀ (z : realRotationTorus L H) (x : T.kernelIdeal),
        α z (Exp (N.equiv x)) = Exp (N.equiv (T.nilradicalRotation H z x))) ∧
      ∀ z, ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ (α z) := by
  obtain ⟨α, hα, he, hs⟩ := exists_nilpotent_automorphism_action
    N T.kernelIdeal_nilpotent Exp hExp (modelNilradicalLinearAction T H N)
    (fun z x y => (modelNilradicalRotation T H N z).map_lie x y)
    (continuous_modelNilradicalRotation T H N)
  refine ⟨α, hα, ?_, hs⟩
  intro z x
  have h := he z (N.equiv x)
  simpa only [modelNilradicalLinearAction_apply, modelNilradicalRotation_apply,
    N.equiv.symm_apply_apply] using h

/-- A fixed choice of the integrated compact action. -/
def nilradicalRotations
    (Exp : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) : realRotationTorus L H →* MulAut N.carrier :=
  (exists_integrated_nilradical_rotations T H N Exp hExp).choose

theorem continuous_nilradicalRotations
    (Exp : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) :
    Continuous (fun p : realRotationTorus L H × N.carrier =>
      nilradicalRotations T H N Exp hExp p.1 p.2) :=
  (exists_integrated_nilradical_rotations T H N Exp hExp).choose_spec.1

theorem nilradicalRotations_exp
    (Exp : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExp : IsGroupExponential Exp) (z : realRotationTorus L H) (x : T.kernelIdeal) :
    nilradicalRotations T H N Exp hExp z (Exp (N.equiv x)) =
      Exp (N.equiv (T.nilradicalRotation H z x)) :=
  (exists_integrated_nilradical_rotations T H N Exp hExp).choose_spec.2.1 z x

end Topology
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntegratedCartanRotations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact Cartan rotations on the original simply connected group -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

set_option maxHeartbeats 1000000 in
omit [H.IsCartanSubalgebra] in
theorem expN_surjective :
    Function.Surjective (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x)) := by
  obtain ⟨c,hc⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal F.N).2
    F.ExpN F.isExpN (F.N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  intro n
  obtain ⟨x,hx⟩ := c.surjective n
  refine ⟨F.N.equiv.symm x,?_⟩
  change F.ExpN (F.N.equiv (F.N.equiv.symm x)) = n
  rw [F.N.equiv.apply_symm_apply]
  rwa [hc] at hx

set_option maxHeartbeats 1000000 in
theorem expD_surjective :
    Function.Surjective (fun h : H => F.ExpD (F.D.equiv h)) := by
  obtain ⟨c,hc⟩ := ((nilpotentPublishedInputs.haar H F.D).2
    F.ExpD F.isExpD (F.D.tangent_nilpotent inferInstance)).1
  intro d
  obtain ⟨x,hx⟩ := c.surjective d
  refine ⟨F.D.equiv.symm x,?_⟩
  change F.ExpD (F.D.equiv (F.D.equiv.symm x)) = d
  rw [F.D.equiv.apply_symm_apply]
  rwa [hc] at hx

/- The compact nilradical rotations commute with the actual Cartan
conjugation, including away from the identity. -/
set_option maxHeartbeats 1000000 in
include hExp in
theorem rotation_commutes_action
    (α : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H →* MulAut F.N.carrier)
    (hα : ∀ z x, α z (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) :
    ∀ z d n, α z (F.action d n) = F.action d (α z n) := by
  intro z
  apply commutes_of_surjective_coordinates
    (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    (fun h : H => F.ExpD (F.D.equiv h)) F.expN_surjective F.expD_surjective
    (α z) (fun d => F.action d) (T.nilradicalRotation H z)
    (fun h x => ⟨adjointLinearMap (E := E) (G := G) (Exp h)
      (x : GroupLieAlgebra (𝓘(ℝ,E)) G),cartan_conjugation_mem hExp h x⟩)
    (hα z) (F.action_cartan_exponential hExp)
  intro h x
  apply Subtype.ext
  exact realTorusOperator_commutes_cartan_conjugation H hExp z h
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G)

/- The compact rotations fix the entire overlap of the two actual factors. -/
set_option maxHeartbeats 1000000 in
include hExp in
theorem exists_compact_rotation_action :
    ∃ β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H →* MulAut G,
      Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H × G =>
        β p.1 p.2) ∧
      ∀ z (x : T.kernelIdeal) d,
        β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
          F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) *
            F.inclusionD d := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  let α := nilradicalRotations T H F.N F.ExpN F.isExpN
  have hα := continuous_nilradicalRotations T H F.N F.ExpN F.isExpN
  have heα := nilradicalRotations_exp T H F.N F.ExpN F.isExpN
  let β := descendedFactorAction F.inclusionN F.inclusionD F.action F.conjugation
    F.surjective α (F.rotation_commutes_action hExp α heα) (F.rotation_fixes_overlap α heα)
  refine ⟨β,continuous_descendedFactorAction F.inclusionN F.inclusionD F.action F.conjugation
    F.surjective α (F.rotation_commutes_action hExp α heα) (F.rotation_fixes_overlap α heα)
    F.closedN.continuous F.closedD.continuous hα F.openProduct,?_⟩
  intro z x d
  change descendedFactorAction _ _ _ _ _ _ _ _ _ _ = _
  rw [descendedFactorAction_product,heα]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FactorRotationCharacter
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invariant compact character for the actual Cartan factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

/- The actual quotient character followed by its compact rotational part. -/

theorem rotationCharacter_invariant
    (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
    (hβ : ∀ z (x : T.kernelIdeal) d,
      β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
        F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d) :
    ∀ z g, F.rotationCharacter (β z g) = F.rotationCharacter g := by
  exact character_invariant_of_factor_coordinates F.inclusionN F.inclusionD
    F.rotationCharacter (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    F.expN_surjective F.surjective (fun z x => T.nilradicalRotation H z x)
    (fun z g => β z g) F.rotationCharacter_nilradical hβ

/- Both ingredients of the rotational modification now exist for the
original group, with the exact invariance required by the graph subgroup. -/

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ActualSmoothRotation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth rotational modification from the actual Cartan factors

The chosen compact action retains its factor formula. This constructs a
smooth graph group; its Lie algebra identification and triangular matrix
realization are separate steps.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)

def factorCompactRotationAction :
    realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G :=
  (F.exists_compact_rotation_action hExp).choose

theorem factorCompactRotationAction_formula :
    ∀ z (x : T.kernelIdeal) d,
      F.factorCompactRotationAction hExp z
        (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d :=
  (F.exists_compact_rotation_action hExp).choose_spec.2

theorem factorCompactRotationAction_invariant :
    ∀ z g, F.rotationCharacter (F.factorCompactRotationAction hExp z g) = F.rotationCharacter g :=
  F.rotationCharacter_invariant (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp)

attribute [local instance] semidirectProductTopology

abbrev SmoothRotationalModification :=
  ↥(rotationalTwist (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp))

@[instance_reducible]
def smoothRotationalModificationChartedSpace : ChartedSpace E (F.SmoothRotationalModification hExp) := by
  let : Fact (Continuous F.rotationCharacter) := ⟨F.continuous_rotationCharacter⟩
  exact rotationalTwistChartedSpace (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp)

attribute [local instance] smoothRotationalModificationChartedSpace

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledSourceCell
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counted samplers on the original quotient/kernel probability cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))

set_option maxHeartbeats 1000000 in
/-- The original quotient and kernel cell underlying the tile probes. -/
def TiledProbeChainData.sourceCell (n : ℕ) : Set (Q.carrier × πQ.ker) :=
  (TiledProbeChainData.sourceQuotientCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale)
    (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D)
    (Q := Q) (chartQ := chartQ)) ×ˢ
  (TiledProbeChainData.sourceKernelCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI)
    (E := E) (β := β) (scale := scale) (ι := ι) (Q := Q)
    (πQ := πQ) (hι := hι) (hrange := hrange) n)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarSourceFrames
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual linked frames on the counted polar source cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Manifold Pointwise Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

variable (D : M.MeasuredCone F (heightConePreimage T eW K))
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  {ε : ℝ} (β : M.ConeIdealBases (heightConePreimage T eW K)) (Rbox : ℝ) (scale : ℕ → ℝ)
  (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
  (P : M.PolarTiledSamplerData (EG := EG) (G := G) (W := W) (I := D.I.carrier) T F hunimod eW K
    (fun v : M.coneWordIdeal (heightConePreimage T eW K) => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN ε β Rbox scale φ)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)

local notation "ZQ" => TiledProbeChainData.sourceQuotientCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ)
local notation "J" => fun n => TiledProbeChainData.sourceKernelCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
  (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
  (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
  (hrange := D.maps.inclusion_range) n
local notation "Y" => fun n : ℕ => {p : D.Q.carrier × D.maps.quotient.ker // p ∈ Set.prod ZQ (J n)}
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (πQ := D.maps.quotient)
  (hι := D.maps.inclusion_closed) (hrange := D.maps.inclusion_range) n
local notation "σ" => TiledProbeChainData.sourceSection
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (chartN := chartN)

variable (Eall : Set W) (γ : M.Bases) (δ : ℝ) (w : W)
  (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier) (base step : ℕ → F.N.carrier)

local notation "Ep" => fun k => (fun z => z + w) '' normalizedPolarTemplates K ε k
local notation "width" => fun i => (1 + δ) * SupportDatum.weightSupport (M.supportIn T hunimod eW) Eall i
local notation "probe" => fun k n (y : Y n) => S n (P.chain.probe n k (ψ n y))

set_option maxHeartbeats 1000000 in
/-- The linked frames on this exact source cell. -/
abbrev PolarTiledSamplerData.LinkedSource :=
  LinkedRootProbeFrames («Y» := Y) T M F hunimod eW bN Ep γ width scale probe base step
    (fun n (y : Y n) => base n * S n ((y.val.2 : F.N.carrier) * σ y.val.1))
    (fun n (y : Y n) => coneProbeSecond (S n).toMulEquiv (base n)
      (D.maps.inclusion (P.anchor n (P.chain.index n (ψ n y).2))) ((S n).symm (step n)))
    (fun n (y : Y n) => coneProbeSecond (S n).toMulEquiv (base n)
      (y.val.2 : F.N.carrier) ((S n).symm (step n)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ray quotients and their ambient actions

The model is chosen from the previously stated nilpotent existence,
integration, and Haar inputs. Its action, section, topology and contraction
are proved properties of that choice.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter TopologicalSpace Topology
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (α₀ : H →ₗ[ℝ] ℝ)

set_option maxHeartbeats 1000000 in
/-- The actual integrated ray quotient, with its descended ambient action. -/
structure RayBoundaryModel where
  cone : M.MeasuredCone F (positiveWeightRay α₀)
  factorAction : F.D.carrier →* MulAut cone.Q.carrier
  action : G →* Equiv.Perm cone.Q.carrier
  equivariant : ∀ d n, factorAction d (cone.maps.quotient n) =
    cone.maps.quotient (F.action d n)
  action_eq : ∀ n d q, action (F.inclusionN n * F.inclusionD d) q =
    cone.maps.quotient n * factorAction d q
  stabilizer : ∀ g, action g 1 = 1 ↔ ∃ n d,
    n ∈ cone.maps.quotient.ker ∧ F.inclusionN n * F.inclusionD d = g

namespace RayBoundaryModel

variable {M F α₀} (R : M.RayBoundaryModel F α₀)

set_option maxHeartbeats 1000000 in
def sectionMap : R.cone.Q.carrier → G := fun q =>
  F.inclusionN (R.cone.maps.sectionMap q)

end RayBoundaryModel

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary volume data constructed on the actual ray quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory TopologicalSpace
open scoped Manifold ENNReal

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} {T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {M : CartanWordModel H}
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} {F : CartanFactorModel H ExpG}
  {eW : HeightSpace T.character ≃ₗ[ℝ] W} {αS αT : W →L[ℝ] ℝ}
  (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  (height : G →* Multiplicative W) (f : P → G → G)

set_option maxHeartbeats 1000000 in
/-- Volume data for the actual source and target ray actions. -/
abbrev RayBoundaryComparison :=
  BoundaryVolumeComparison RS.action RT.action αS αT height f

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ShadowExponentialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear coordinates for the two real-shadow exponential factors -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)

def shadowKernelParameter : L →ₗ[ℝ] A := (shadowRepresentationParameter T H j).comp
  (T.kernelIdeal.incl.toLinearMap.comp (T.kernelComponent H))

end PolycyclicRecognition

end

end OAI
end


