-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogLiftPpZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogLiftPpZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:10.622871+00:00
-- url     : https://prove2.me/theorems/b728e274-cb98-41b7-be23-363dd0c137f6
-- title:
--   Log Lift Pp Zero
-- statement:
--   Definitions and structural lemmas for Log Lift Pp Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogLiftPpZero.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
section LogMul
variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)
end LogMul
end GlobalTheory.DI


