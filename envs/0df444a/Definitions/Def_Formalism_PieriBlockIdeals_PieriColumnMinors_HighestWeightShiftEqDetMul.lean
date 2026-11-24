-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:49:49.581584+00:00
-- url     : https://prove2.me/theorems/9728c1ab-b746-426c-ad33-b581fd51015e
-- title:
--   Highest Weight Shift Eq Det Mul
-- statement:
--   Definitions and structural lemmas for Highest Weight Shift Eq Det Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
def genericMatrix' (R : Type) [CommRing R] (r : ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) R) :=
  Matrix.of fun p q : Fin r => (X (p, q) : MvPolynomial (Fin r × Fin r) R)
def genericDet (R : Type) [CommRing R] (r : ℕ) : MvPolynomial (Fin r × Fin r) R :=
  (genericMatrix' R r).det
end Formalism.CohomologicalDescent.LA


