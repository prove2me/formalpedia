-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:14.343557+00:00
-- url     : https://prove2.me/theorems/c5aa1095-bcb5-4982-9664-c5dd85c21462
-- title:
--   Hecke Assoc
-- statement:
--   Definitions and structural lemmas for Hecke Assoc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeAssoc.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)
end Formalism.UG.P


