-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:26.651569+00:00
-- url     : https://prove2.me/theorems/1cf54e23-62d9-4e9e-8018-76f39619c2aa
-- title:
--   Spherical A
-- statement:
--   Definitions and structural lemmas for Spherical A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
namespace Formalism.UG.P
section Upper
variable {L : Type} [Field L] {n : ℕ}
end Upper
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Formalism.UG.P


