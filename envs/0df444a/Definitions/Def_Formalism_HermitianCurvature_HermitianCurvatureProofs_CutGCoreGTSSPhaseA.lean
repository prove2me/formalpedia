-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSPhaseA
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSPhaseA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:03.347595+00:00
-- url     : https://prove2.me/theorems/1d204303-bc10-40f6-ab2a-cfb65916bbb4
-- title:
--   Cut GCore GTSSPhase A
-- statement:
--   Definitions and structural lemmas for Cut GCore GTSSPhase A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSPhaseA.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
def height (P : M.Par) (ρ : M.Ty P) : ℕ := ∑ i, ((ρ i : Fin _) : ℕ)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh


