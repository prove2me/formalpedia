-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicHermitianFormGaloisMemOfMemCompletion
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicHermitianFormGaloisMemOfMemCompletion
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:39:29.062834+00:00
-- url     : https://prove2.me/theorems/5718e187-b878-48eb-ae08-fbbdfeb02df8
-- title:
--   Adelic Hermitian Form Galois Mem Of Mem Completion
-- statement:
--   Definitions and structural lemmas for Adelic Hermitian Form Galois Mem Of Mem Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicHermitianFormGaloisMemOfMemCompletion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
end
end GlobalTheory.AdLat


