-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:35:07.8516+00:00
-- url     : https://prove2.me/theorems/5a75bc78-2a98-4bfc-822e-230130d725ef
-- title:
--   PSnapper Diff Poly
-- statement:
--   Definitions and structural lemmas for PSnapper Diff Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
namespace SnapperDiffPoly
def numPt {t : ℕ} (n : Fin t → ℕ) (c : ℤ) : Fin (t + 1) → ℚ :=
  Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)
end SnapperDiffPoly
end
end GroundTheory.Heights₂.Heights.Kleiman


