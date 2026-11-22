-- Prove2me | Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
-- name    : Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:13.37905+00:00
-- url     : https://prove2.me/theorems/00746c97-5cec-4e04-8d9e-af4050d7a77b
-- title:
--   MQKummer
-- statement:
--   Definitions and structural lemmas for MQKummer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.Q3
section KummerAux
variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
end KummerAux
section KummerInd
variable {E : Type*} [Field E] [CharZero E]
def mqkField (F : Type*) [Field F] [Algebra F E] {k : ℕ} (α : Fin k → E) (T : Finset (Fin k)) : IntermediateField F E :=
  IntermediateField.adjoin F (α '' (T : Set (Fin k)))
end KummerInd
end Formalism.Q3


