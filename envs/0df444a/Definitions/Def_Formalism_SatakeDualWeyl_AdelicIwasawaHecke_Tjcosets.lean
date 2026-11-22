-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:32.351673+00:00
-- url     : https://prove2.me/theorems/503bf526-8448-4400-9f9e-69533c1e5e5f
-- title:
--   Tjcosets
-- statement:
--   Definitions and structural lemmas for Tjcosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
namespace Formalism.UG.P
open Formalism.UG
section Adic
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
instance tjcosets_isLocalRing : IsLocalRing (Ov F v) :=
  inferInstanceAs (IsLocalRing (v.adicCompletionIntegers F))
end Adic
end Formalism.UG.P


