-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:06.54135+00:00
-- url     : https://prove2.me/theorems/ed16ef45-2736-4a64-928e-7a865bd91010
-- title:
--   St Perfect Field Extension Formally Smooth
-- statement:
--   Definitions and structural lemmas for St Perfect Field Extension Formally Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPerfectFieldExtensionFormallySmooth.lean

import Mathlib
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
def PerfectFieldExtensionFormallySmooth.Statement : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [PerfectField F], Algebra.FormallySmooth F K
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


