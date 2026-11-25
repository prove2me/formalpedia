-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:41.294226+00:00
-- url     : https://prove2.me/theorems/fa6862e3-6d08-533c-9bb2-fa4f897d0d14
-- title:
--   Core Cas W
-- statement:
--   Definitions and structural lemmas for Core Cas W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
def rho2 {r s : ℕ} : Ix r s → ℚ
  | .inl k => (r : ℚ) - 1 - 2 * (k : ℕ)
  | .inr l => (s : ℚ) - 1 - 2 * (l : ℕ)
end PositivityTheory.KReal
end


