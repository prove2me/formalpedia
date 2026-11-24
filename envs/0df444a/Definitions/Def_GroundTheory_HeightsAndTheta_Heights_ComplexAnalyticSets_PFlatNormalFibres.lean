-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:01.133798+00:00
-- url     : https://prove2.me/theorems/4c56eb0e-cc51-41d1-ae67-e281c25d5a68
-- title:
--   PFlat Normal Fibres
-- statement:
--   Definitions and structural lemmas for PFlat Normal Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatNormalFibres.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreRFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence
noncomputable def localizationAtMaximalEquiv (B : Type*) [CommRing B] [IsLocalRing B] :
    Localization.AtPrime (maximalIdeal B) ≃+* B :=
  (IsLocalization.atUnits B (maximalIdeal B).primeCompl (fun x hx => by
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mem_submonoid_iff] using hx)).toRingEquiv.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


