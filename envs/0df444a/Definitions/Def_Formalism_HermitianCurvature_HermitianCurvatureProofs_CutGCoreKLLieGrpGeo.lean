-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLLieGrpGeo
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLLieGrpGeo
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:19.707054+00:00
-- url     : https://prove2.me/theorems/534c340a-a96b-5585-82bd-bfe060264eeb
-- title:
--   Cut GCore KLLie Grp Geo
-- statement:
--   Definitions and structural lemmas for Cut GCore KLLie Grp Geo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLLieGrpGeo.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace KLG
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}
def cvec2 (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec k r z) (fun _ => e)
def cvec2' (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec' k r z) (fun _ => e)
end KLG
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


