-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PNoLogOde
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PNoLogOde
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:28.286475+00:00
-- url     : https://prove2.me/theorems/1096827a-b29e-4227-bbae-3908dcb04970
-- title:
--   PNo Log Ode
-- statement:
--   Definitions and structural lemmas for PNo Log Ode, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
def pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ := p.sum fun k a => a * f k t
def pevL (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ[X] →ₗ[ℂ] ℂ := Polynomial.lsum fun n => f n t • LinearMap.id
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
end


