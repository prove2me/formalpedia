-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:29.401831+00:00
-- url     : https://prove2.me/theorems/e57e16e1-ce29-4ae8-92f5-4b55b824564f
-- title:
--   Torsion Norm Iter Proof
-- statement:
--   Definitions and structural lemmas for Torsion Norm Iter Proof, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean

import Definitions.Def_Formalism_TorsionNormIteration_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
section LT
variable {π : K} {q : ℕ} {e : Polynomial K}
end LT
end Formalism.LT.TorsProof
open Formalism.LT.TorsProof


