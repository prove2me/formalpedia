-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:11.462102+00:00
-- url     : https://prove2.me/theorems/06125fac-c437-4007-a4a9-536c61338504
-- title:
--   Satake Res
-- statement:
--   Definitions and structural lemmas for Satake Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeRes.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
def satakeIota : 𝓞 F →+* Ov F v := algebraMap (𝓞 F) (v.adicCompletionIntegers F)
end Formalism.UG.P


