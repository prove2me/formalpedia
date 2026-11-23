-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:47.690283+00:00
-- url     : https://prove2.me/theorems/d1a09de7-6b77-49c5-a816-66664e0fec37
-- title:
--   FIwasawa E
-- statement:
--   Definitions and structural lemmas for FIwasawa E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaE.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaStepB
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
end FIwasawaStepB
end Formalism.UG.P


