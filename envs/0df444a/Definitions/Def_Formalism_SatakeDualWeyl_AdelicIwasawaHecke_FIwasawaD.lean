-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:24.229823+00:00
-- url     : https://prove2.me/theorems/51a8d256-4ae9-4ebd-9a35-44e6c537f13d
-- title:
--   FIwasawa D
-- statement:
--   Definitions and structural lemmas for FIwasawa D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaD.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
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
section FIwasawaStep
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
end FIwasawaStep
end Formalism.UG.P


