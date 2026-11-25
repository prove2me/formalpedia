-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:27:57.986018+00:00
-- url     : https://prove2.me/theorems/2e512ab7-8f03-44cf-b6e4-bf06c791317e
-- title:
--   Snapper Diff Poly St
-- statement:
--   Definitions and structural lemmas for Snapper Diff Poly St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperDiffPolySt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
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
universe u v w
def SnapperDiffPoly.Statement : Prop :=
  ∀ (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) (μ : Fin t → ℤ),
    IsNumPolyLT t D (fun n c => f n (c + 1) - f n c) →
    (∀ j, IsNumPolyLT t D (fun n c => f (Function.update n j (n j + 1)) (c + μ j) - f n c)) →
    IsNumPolyLT t (D + 1) f
end
end GroundTheory.Heights₂.Heights.Kleiman


