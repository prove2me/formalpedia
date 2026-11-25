-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:14.410321+00:00
-- url     : https://prove2.me/theorems/25d8b1ac-7020-4286-b510-d9525075e868
-- title:
--   Core Harm
-- statement:
--   Definitions and structural lemmas for Core Harm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
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
namespace Harm
section MP
variable {σ : Type}
end MP
variable {p q r s : ℕ}
def low1 (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((b, c) : Ln p q r s) = true then
    (pderiv ((a, c) : Ln p q r s)).toLinearMap * (pderiv ((b, c) : Ln p q r s)).toLinearMap
  else 0
end Harm
open Harm
variable {p q r s : ℕ}
end PositivityTheory.KReal
end


