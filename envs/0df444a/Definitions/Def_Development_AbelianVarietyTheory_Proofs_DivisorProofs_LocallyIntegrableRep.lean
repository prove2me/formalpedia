-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:39.988055+00:00
-- url     : https://prove2.me/theorems/8a4cbeb4-c72f-4fd2-ab5f-3df45d1bfc10
-- title:
--   Locally Integrable Rep
-- statement:
--   Definitions and structural lemmas for Locally Integrable Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyIntegrableRep.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.LocRep
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
end GlobalTheory.LocRep


