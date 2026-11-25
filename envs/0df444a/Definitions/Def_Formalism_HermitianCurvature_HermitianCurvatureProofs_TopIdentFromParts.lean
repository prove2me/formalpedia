-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopIdentFromParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TopIdentFromParts
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:44:05.222944+00:00
-- url     : https://prove2.me/theorems/463e284f-102d-483b-a3bc-b937ba9d4b77
-- title:
--   Top Ident From Parts
-- statement:
--   Definitions and structural lemmas for Top Ident From Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopIdentFromParts.lean

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
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
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
end
end Formalism.FourierDecayAlt.P5


