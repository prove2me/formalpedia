-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:52:25.257367+00:00
-- url     : https://prove2.me/theorems/6744efc9-3c88-4a17-956e-a70bc3e91917
-- title:
--   Pt Mat Is Unit
-- statement:
--   Definitions and structural lemmas for Pt Mat Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/StabilizerIndexVolumes/PtMatIsUnit.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]
def antiB (t : K) (s : ℕ) : Matrix (Fin s) (Fin s) K := fun i j => if i.val + j.val + 1 = s then t else 0
end Formalism.L2.SG.Pf.StabilizerIndexVolumes


