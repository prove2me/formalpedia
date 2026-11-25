-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:32.296384+00:00
-- url     : https://prove2.me/theorems/8f8eb38d-759b-53d1-8f90-33f93b95ea49
-- title:
--   Rel Index Eq Index Of Mul
-- statement:
--   Definitions and structural lemmas for Rel Index Eq Index Of Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]
abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt


