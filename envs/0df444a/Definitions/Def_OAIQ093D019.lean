-- Prove2me | Definitions.Def_OAIQ093D019
-- name    : OAIQ093D019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:44:32.853208+00:00
-- url     : https://prove2.me/theorems/05e188b6-4328-4309-8900-6bf4fea5c8ea
-- title:
--   Definitions bundle OAIQ093D019 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 inductive type or structure. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMaps`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`PolycyclicRecognition_Geometry_CartanMeasuredCone`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanMeasuredCone.lean).
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundle `OAIQ093D016` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ093D027`; the statement `OAI_PolycyclicRecognition_CartanWordModel_ray_boundary_homeomorphisms_of_compact_shadows`; the proofs of `OAI_PolycyclicRecognition_CartanWordModel_exists_polar_flow_tiling` and `OAI_PolycyclicRecognition_CartanWordModel_ray_boundary_homeomorphisms_of_compact_shadows`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D016

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredCone
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
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

set_option maxHeartbeats 1000000 in
/-- Exponential and group maps for the one fixed mixed-word ideal. -/
structure ConeGroupMaps
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (I : NilpotentLieModel (M.coneWordIdeal C)) where
  expQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier
  expI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier
  isExpQ : IsGroupExponential expQ
  isExpI : IsGroupExponential expI
  chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier
  chartI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier ≃ₜ I.carrier
  chartQ_eq : ∀ v, chartQ v = expQ v
  chartI_eq : ∀ v, chartI v = expI v
  quotient : F.N.carrier →* Q.carrier
  quotient_continuous : Continuous quotient
  sectionMap : ContinuousMap Q.carrier F.N.carrier
  section_rightInverse : ∀ q, quotient (sectionMap q) = q
  kernel_eq : (quotient.ker : Set F.N.carrier) = F.ExpN ''
    (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H)))
  quotient_exp : ∀ v, quotient (F.ExpN (F.N.equiv v)) =
    expQ (Q.equiv (M.coneProjection C v))
  inclusion : I.carrier →* F.N.carrier
  inclusion_closed : Topology.IsClosedEmbedding inclusion
  inclusion_exp : ∀ v : M.coneWordIdeal C,
    inclusion (expI (I.equiv v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H))
  inclusion_range : range inclusion = (quotient.ker : Set F.N.carrier)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end


