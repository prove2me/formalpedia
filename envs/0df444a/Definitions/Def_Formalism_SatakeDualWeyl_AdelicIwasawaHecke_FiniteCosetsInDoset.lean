-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:19.465351+00:00
-- url     : https://prove2.me/theorems/9d2737af-eff1-4d60-85bd-d1a4876e5c8e
-- title:
--   Finite Cosets In Doset
-- statement:
--   Definitions and structural lemmas for Finite Cosets In Doset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FiniteCosetsInDoset.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
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
variable {G : Type} [Group G]
abbrev conjInter (K : Subgroup G) (s : G) : Subgroup K :=
  (K.map (MulAut.conj s).toMonoidHom).subgroupOf K
end Formalism.UG.P


