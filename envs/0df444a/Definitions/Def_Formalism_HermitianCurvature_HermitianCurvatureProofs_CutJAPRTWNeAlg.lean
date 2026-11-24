-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:48.310796+00:00
-- url     : https://prove2.me/theorems/3195d02c-8617-485d-a3a8-59bfd4a868d3
-- title:
--   Cut JAPRTWNe Alg
-- statement:
--   Definitions and structural lemmas for Cut JAPRTWNe Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
section lemmas
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end lemmas
section inj
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
  [FiniteDimensional ℂ V']
end inj
section core
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
  [FiniteDimensional ℂ V']
end core
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW


