-- Prove2me | Definitions.Def_OAIQ093D021
-- name    : OAIQ093D021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:37:11.487833+00:00
-- url     : https://prove2.me/theorems/cb82bf96-1281-4975-b6fd-dbb0ac8af372
-- title:
--   Definitions bundle OAIQ093D021 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 21 definitions, 1 inductive type or structure, 1 instance and 8 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.PolarConeModelInputs.model`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.factorParameter`, `OAI.PolycyclicRecognition.IntegralNilshadowData`, `OAI.PolycyclicRecognition.IntegralNilshadowData.completedAction`, `OAI.PolycyclicRecognition.IntegralNilshadowData.completedLieAction`, `OAI.PolycyclicRecognition.IntegralNilshadowData.completionSemidirectMap`, `OAI.PolycyclicRecognition.IntegralNilshadowData.factorEmbedding`, `OAI.PolycyclicRecognition.IntegralNilshadowData.height`, `OAI.PolycyclicRecognition.IntegralNilshadowData.heightLinear`, `OAI.PolycyclicRecognition.IntegralNilshadowData.heightProjection`, `OAI.PolycyclicRecognition.IntegralNilshadowData.integralAction`, `OAI.PolycyclicRecognition.IntegralNilshadowData.inverseScaledHeight`, `OAI.PolycyclicRecognition.IntegralNilshadowData.quotientBasis`, `OAI.PolycyclicRecognition.IntegralNilshadowData.quotientSection`, `OAI.PolycyclicRecognition.IntegralNilshadowData.system`, `OAI.PolycyclicRecognition.IntegralNilshadowData.twistedSystem`, `OAI.PolycyclicRecognition.JointFixedReductionData.residualEmbedding`, `OAI.PolycyclicRecognition.JointFixedReductionData.residualLayer`, `OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerEquiv`, `OAI.PolycyclicRecognition.JointFixedReductionData.residualLayerProjection`, `OAI.PolycyclicRecognition.JointFixedReductionData.residualSystem`, `OAI.PolycyclicRecognition.scaleRealHeight`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`PolycyclicRecognition_Algebra_ComplexFactorLocalChart`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/ComplexFactorLocalChart.lean), [`PolycyclicRecognition_Algebra_ResidualLowerCentralLayers`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/ResidualLowerCentralLayers.lean), [`PolycyclicRecognition_Geometry_CartanMeasuredCone`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanMeasuredCone.lean), [`PolycyclicRecognition_Geometry_CartanMeasuredConeRealization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanMeasuredConeRealization.lean), [`PolycyclicRecognition_Geometry_CartanPolarConeModels`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarConeModels.lean), [`PolycyclicRecognition_Lattices_IntegralNilshadow`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Lattices/IntegralNilshadow.lean), [`PolycyclicRecognition_Lattices_JointFixedReductionData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Lattices/JointFixedReductionData.lean), [`PolycyclicRecognition_Lattices_NilshadowHeight`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Lattices/NilshadowHeight.lean), [`PolycyclicRecognition_Lattices_NilshadowPowerGraph`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Lattices/NilshadowPowerGraph.lean).
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D027` and `OAIQ093D020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ093D024`; the statements `OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.hasMFDerivAt_factorParameter`; the proofs of `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model` and `OAI.PolycyclicRecognition.ComplexWeightFactorModel.hasMFDerivAt_factorParameter`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredCone
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual ideal, quotient and Haar measures for a fixed cone -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ))

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
/-- The fixed cone's group models and compatible Haar measures follow from
Lie integration and exponential Haar measure. Only the original published
inputs are used; arbitrary pure-word sections can be installed afterward. -/
theorem nonempty_measuredCone
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (existQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (integrateQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := F.N.modelSpace) (N := F.N.carrier)
        (EG := Q.modelSpace) (G := Q.carrier))
    (existI : NilpotentLieExistenceInput (M.coneWordIdeal C))
    (haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (integrateI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
        (EG := F.N.modelSpace) (G := F.N.carrier))
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : F.N.carrier →* Aˣ)
    (hρ : Function.Injective ρ)
    (hmatch : ∀ v, ρ (F.ExpN (F.N.equiv v)) = algebraExpUnit (j v)) :
    Nonempty (M.MeasuredCone F C) := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨Q, expQ, heQ, π, σ, hπ, hπe, hσ, _, hker, _⟩ :=
    M.exists_cone_group_quotient C F.N F.ExpN F.isExpN haarN existQ haarQ integrateQ
  obtain ⟨I, expI, heI, ι, hi, _, hie, hir⟩ :=
    M.exists_cone_ideal_group C F.N F.ExpN F.isExpN haarN π hker existI haarI integrateI
  let : IsTopologicalGroup I.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, I.modelSpace)) ⊤
  obtain ⟨⟨chartQ, hcQ⟩, hμQ⟩ := (haarQ Q).2 expQ heQ
    (Q.tangent_nilpotent (M.coneQuotient_nilpotent C))
  obtain ⟨⟨chartI, hcI⟩, _⟩ := (haarI I).2 expI heI
    (I.tangent_nilpotent (M.coneIdeal_nilpotent C))
  obtain ⟨⟨chartN, hcN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (LieModule.IsNilpotent.mk _ M.bound_zero))
  have hbijN : Function.Bijective F.ExpN := funext hcN ▸ chartN.bijective
  obtain ⟨μI, hI, hK, hconj, hright⟩ :=
    M.exists_cone_kernel_invariant_haar C I.equiv expI heI (haarI I)
      (finBasis ℝ (M.coneWordIdeal C)) π ι hi hir (F.ExpN ∘ F.N.equiv)
      (hbijN.comp F.N.equiv.bijective).surjective hie j ρ hρ hmatch
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map Q.equiv.toLinearEquiv
  let μQ := Measure.map (expQ ∘ bQ.equivFun.symm) volume
  have hQ : μQ.IsHaarMeasure := hμQ _ bQ
  let maps : M.ConeGroupMaps F C Q I := {
    expQ := expQ, expI := expI, isExpQ := heQ, isExpI := heI
    chartQ := chartQ, chartI := chartI, chartQ_eq := hcQ, chartI_eq := hcI
    quotient := π, quotient_continuous := hπ.continuous
    sectionMap := σ, section_rightInverse := hσ, kernel_eq := hker, quotient_exp := hπe
    inclusion := ι, inclusion_closed := hi, inclusion_exp := hie, inclusion_range := hir }
  exact ⟨{
    Q := Q, I := I, maps := maps
    measures := {
      measureQ := μQ, measureI := μI, haarQ := hQ, haarI := hI
      haarKernel := hK, conjugation_invariant := hconj, kernel_rightInvariant := hright } }⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredConeRealization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ))

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped Matrix.Norms.Operator

set_option maxHeartbeats 1000000 in
/-- The precise published linear realization supplies the faithful root
representation required by the measured cone construction. The choice of
height and every metric estimate remain separate from this input. -/
theorem nonempty_measuredCone_of_published_realization
    [SimplyConnectedSpace G] {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (existQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (integrateQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := F.N.modelSpace) (N := F.N.carrier)
        (EG := Q.modelSpace) (G := Q.carrier))
    (existI : NilpotentLieExistenceInput (M.coneWordIdeal C))
    (haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (integrateI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
        (EG := F.N.modelSpace) (G := F.N.carrier))
    : Nonempty (M.MeasuredCone F C) := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  have hr (v : cartanRootIdeal H) :
      (ρ.comp F.inclusionN) (F.ExpN (F.N.equiv v)) =
        algebraExpUnit ((j.comp (cartanRootIdeal H).incl) v) := by
    change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = algebraExpUnit (j v)
    rw [F.compatibleN, hmatch]
  exact M.nonempty_measuredCone (A := Matrix (Fin m) (Fin m) ℝ) F C
    haarN existQ haarQ integrateQ existI haarI integrateI
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) hr

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeModels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published inputs for the finite polar-cone models

This record only groups the already stated nilpotent existence, integration
and exponential Haar inputs. It contains no metric or profile conclusion.
It is instantiated separately for each ray or two-ray cone used below.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (C : Set (H →ₗ[ℝ] ℝ))

variable [SimplyConnectedSpace G] {a : ℕ}
  (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (inputs : M.PolarConeModelInputs F C)

set_option maxHeartbeats 1000000 in
/-- Choose only the concrete measured cone required by the application. -/
def PolarConeModelInputs.model : M.MeasuredCone F C :=
  Classical.choice (M.nonempty_measuredCone_of_published_realization F C T hExp realize
    haarN inputs.existsQ inputs.haarQ inputs.integratesQ
    inputs.existsI inputs.haarI inputs.integratesI)

end PolycyclicRecognition.CartanWordModel

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

def factorParameter (x : E) : G :=
  F.inclusionN (F.ExpN (F.kernelParameter x)) *
    F.inclusionD (F.ExpD (F.cartanParameter x))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedReductionData
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Constructed joint-fixed residual data for an actual extension

The residual group is defined by the actual section factors and embeds in the
original extension. The prescribed quotient lifts act unipotently on its
kernel Lie algebra.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

namespace JointFixedReductionData
variable {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}
  (D : JointFixedReductionData E hsmooth qs)

omit [LieRing.IsNilpotent L] in
theorem action_commutes (S : L ≃ₗ⁅ℝ⁆ L) (hS : S ∈ D.operators) (q : Q) :
    Commute S.toLinearMap (D.action q).toLinearMap :=
  (mem_semisimpleActionCentralizer_iff E S _ _).mp (D.centralizes S hS q)

def residualSystem : NonabelianFactorSystem (jointFixedLieSubalgebra D.operators) Q :=
  jointFixedFactorSystem (GroupExtensionSection.factorSystem E D.sectionMap D.normalized)
    D.action (fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm)
    D.operators D.action_commutes D.factorsFixed

def residualEmbedding : FactorExtension D.residualSystem →* G :=
  jointFixedExtensionEmbedding E D.sectionMap D.normalized D.action
    (fun _ _ => (polynomialModelLieEquiv_apply _ _ _).symm)
    D.operators D.action_commutes D.factorsFixed

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ResidualLowerCentralLayers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction_embed _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Group commutators on the joint-fixed lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

def residualLayer (k : ℕ) : Subgroup (FactorExtension D.residualSystem) :=
  (D.residualKernelLayer k).map (FactorExtension.inl D.residualSystem)

instance residualLayer_normal (k : ℕ) : (D.residualLayer k).Normal where
  conj_mem g hg a := by
    obtain ⟨x, hx, rfl⟩ := hg
    let E₀ := FactorExtension.groupExtension D.residualSystem
    refine ⟨E₀.conjAct a x, ?_, ?_⟩
    · rw [FactorExtension.conjugation_inl]
      exact polynomialSubalgebra_conjugate_mem _ _ _
        (jointFixed_action_preserves_lowerCentral D.operators (D.action a.right)
          (fun S hS => D.action_commutes S hS _) k x hx) a.left
    · exact E₀.inl_conjAct_comm

def residualLayerEquiv (k : ℕ) : D.residualKernelLayer k ≃* D.residualLayer k :=
  (D.residualKernelLayer k).equivMapOfInjective _ (FactorExtension.inl_injective _)

def residualLayerProjection (k : ℕ) : D.residualLayer k →*
    Multiplicative (D.lowerCentralLayer k) :=
  (polynomialLowerCentralProjection _ k).comp (D.residualLayerEquiv k).symm.toMonoidHom

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
@[simp] theorem residualLayerProjection_equiv (k : ℕ) (x : D.residualKernelLayer k) :
    D.residualLayerProjection k (D.residualLayerEquiv k x) =
      polynomialLowerCentralProjection _ k x := by
  simp only [residualLayerProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_IntegralNilshadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the nilshadow of an integral abelian extension

Both the section and the removed action are constructed from the original
extension. The twisted group has a nilpotent real completion of the correct
dimension. Its removed action extends, and the original group embeds faithfully
in the corresponding semidirect product. The quotient here is still integral.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group G] {n : ℕ}

structure IntegralNilshadowData (E : GroupExtension L G (IntegralLatticeGroup n)) where
  sectionMap : E.Section
  normalized : sectionMap 1 = 1
  removed : IntegralLatticeGroup n →* MulAut L
  commutes : ∀ q r, Commute
    ((GroupExtensionSection.factorSystem E sectionMap normalized).action q) (removed r)
  fixes : ∀ q r s, removed q
    ((GroupExtensionSection.factorSystem E sectionMap normalized).factor r s) =
      (GroupExtensionSection.factorSystem E sectionMap normalized).factor r s
  smooth : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (removed q)
  twist_smooth : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞
    (((GroupExtensionSection.factorSystem E sectionMap normalized).twist removed commutes fixes).action q)
  twist_nilpotent : Group.IsNilpotent (FactorExtension
    ((GroupExtensionSection.factorSystem E sectionMap normalized).twist removed commutes fixes))
  completion : NilpotentKernelCompletion (FactorExtension.inl
    ((GroupExtensionSection.factorSystem E sectionMap normalized).twist removed commutes fixes))
  dimension : completion.dimension = Module.finrank ℝ L + n

namespace IntegralNilshadowData
variable {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)
omit [LieRing.IsNilpotent L]

abbrev system := GroupExtensionSection.factorSystem E D.sectionMap D.normalized
abbrev twistedSystem := D.system.twist D.removed D.commutes D.fixes
abbrev integralAction := factorTwistAction D.system D.removed D.commutes D.fixes

theorem integralAction_kernel_smooth (q : IntegralLatticeGroup n) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, D.completion.carrier)) ∞
      ((D.completion.embed.comp (D.integralAction q).toMonoidHom).comp
        (FactorExtension.inl D.twistedSystem)) := by
  exact D.completion.kernel_smooth.comp (D.smooth q)

def completedAction : IntegralLatticeGroup n →* MulAut D.completion.carrier :=
  D.completion.extendedAction D.integralAction D.integralAction_kernel_smooth

theorem completedAction_smooth (q : IntegralLatticeGroup n) :
    ContMDiff (𝓘(ℝ, D.completion.carrier)) (𝓘(ℝ, D.completion.carrier)) ∞ (D.completedAction q) :=
  D.completion.extendedAction_smooth D.integralAction D.integralAction_kernel_smooth q

def completionSemidirectMap :
    (FactorExtension D.twistedSystem ⋊[D.integralAction] IntegralLatticeGroup n) →*
      (D.completion.carrier ⋊[D.completedAction] IntegralLatticeGroup n) :=
  SemidirectProduct.map D.completion.embed (MonoidHom.id _) (by
    intro q
    apply MonoidHom.ext
    intro x
    exact (D.completion.extendedAction_embed D.integralAction
      D.integralAction_kernel_smooth q x).symm)

end IntegralNilshadowData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed linear section of the nilshadow height

The section vectors are the logarithmic coordinates of the actual integral
quotient lifts. The removed action fixes them, as well as the height map.
-/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

def height : D.completion.carrier →* AbelianRealSpace n :=
  (D.completion.exists_height (FactorExtension.groupExtension D.twistedSystem)).choose

theorem height_smooth :
    ContMDiff (𝓘(ℝ, D.completion.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ D.height :=
  (D.completion.exists_height (FactorExtension.groupExtension D.twistedSystem)).choose_spec.1

theorem height_embed (g : FactorExtension D.twistedSystem) :
    D.height (D.completion.embed g) = integralRealHeight g.right :=
  (D.completion.exists_height (FactorExtension.groupExtension D.twistedSystem)).choose_spec.2 g

def heightLinear : D.completion.carrier →ₗ[ℝ] AbelianRealSpace n :=
  (polynomialModelLieHom D.height D.height_smooth).toLinearMap

def quotientBasis (n : ℕ) : Module.Basis (Fin n) ℝ (AbelianRealSpace n) := Pi.basisFun ℝ (Fin n)

def quotientSection : AbelianRealSpace n →ₗ[ℝ] D.completion.carrier :=
  (quotientBasis n).constr ℝ
    (fun i => D.completion.embed ⟨1, integralLatticeGenerator n i⟩)

def completedLieAction (q : IntegralLatticeGroup n) :
    D.completion.carrier ≃ₗ⁅ℝ⁆ D.completion.carrier :=
  polynomialModelLieEquiv (D.completedAction q) (D.completedAction_smooth q)

def heightProjection : Module.End ℝ D.completion.carrier :=
  D.quotientSection.comp D.heightLinear

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilshadowPowerGraph
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the finite-power extension in the real invariant graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

def scaleRealHeight (n : ℕ) (a : ℝ) : AbelianRealSpace n →* Multiplicative (Fin n → ℝ) where
  toFun x := Multiplicative.ofAdd (a • x)
  map_one' := by
    apply Multiplicative.ext
    exact smul_zero a
  map_mul' x y := by
    apply Multiplicative.ext
    exact smul_add a x y

namespace IntegralNilshadowData
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

def inverseScaledHeight (m : ℕ) : D.completion.carrier →* Multiplicative (Fin n → ℝ) :=
  (scaleRealHeight n (-((m : ℝ)⁻¹))).comp D.height

def factorEmbedding : FactorExtension D.system →*
    (D.completion.carrier ⋊[D.completedAction] IntegralLatticeGroup n) :=
  D.completionSemidirectMap.comp
    (factorTwistGraph D.system D.removed D.commutes D.fixes)

end IntegralNilshadowData
end PolycyclicRecognition

end

end OAI
end


