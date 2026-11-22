-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:19:44.129038+00:00
-- url     : https://prove2.me/theorems/1737f291-4e55-481c-8243-ff691efe58e9
-- title:
--   Stdform
-- statement:
--   Definitions and structural lemmas for Stdform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.UG.P
open Formalism.UG
section Stdform
variable {n : Type} [Fintype n] [DecidableEq n]
def stdformQ (M : Matrix n n ℂ) (y : n → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * M i j * y j).re
section Emb
variable {E : Type} [Field E]
end Emb
end Stdform
section Inv
variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]
end Inv
section Sign
variable {n : Type} [Fintype n] [DecidableEq n]
end Sign
end Formalism.UG.P


