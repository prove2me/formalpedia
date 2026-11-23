-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsContOnOfLocal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsContOnOfLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:39.133069+00:00
-- url     : https://prove2.me/theorems/ac3f6f2f-d349-409f-9bc1-840e92008fb3
-- title:
--   Is Cont On Of Local
-- statement:
--   Definitions and structural lemmas for Is Cont On Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsContOnOfLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
namespace GlobalTheory.WeilCont
variable (F : Type) [Field F] [NumberField F] {κ : Type}
def adeleJoin (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)
end GlobalTheory.WeilCont
end


