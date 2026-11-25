-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Imports
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Imports
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:12.169139+00:00
-- url     : https://prove2.me/theorems/d85b4ede-c1a9-4cd2-8c87-d5640e889685
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Imports.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def Kr (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p : Mt k r × Mt k r, star (psi k r Bs.z' cStd (Matrix.of p.2)) •
    (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹) ∂(Bs.μW'.prod Bs.μN)
end Formalism.FourierDecayAlt.P.PBG


