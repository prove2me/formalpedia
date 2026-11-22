-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
-- name    : Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:02.678151+00:00
-- url     : https://prove2.me/theorems/28c15a23-1613-486d-bd0b-cfa87ea09b37
-- title:
--   Diagonal Entry Eq Of Modular Relation
-- statement:
--   Definitions and structural lemmas for Diagonal Entry Eq Of Modular Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
section Alg
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
end Alg
section Mod
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
end Mod
end Formalism.YangianSpanCharacter.P


