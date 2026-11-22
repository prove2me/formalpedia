-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:19:30.600521+00:00
-- url     : https://prove2.me/theorems/ceb60e87-db58-42f2-930d-295403b94f86
-- title:
--   Glint Princ Rel Index Ne Zero
-- statement:
--   Definitions and structural lemmas for Glint Princ Rel Index Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.UG.P
open Formalism.UG
section Generic
variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
end Generic
section Adic
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Adic
end Formalism.UG.P


