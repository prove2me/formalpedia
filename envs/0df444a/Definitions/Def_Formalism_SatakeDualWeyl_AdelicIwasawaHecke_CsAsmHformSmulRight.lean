-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsAsmHformSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:33.862482+00:00
-- url     : https://prove2.me/theorems/d9c82171-24ae-476e-b84a-b0a148c602fe
-- title:
--   Cs Asm Hform Smul Right
-- statement:
--   Definitions and structural lemmas for Cs Asm Hform Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsAsmHformSmulRight.lean

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG Formalism.UG.CS
end Formalism.UG.P


