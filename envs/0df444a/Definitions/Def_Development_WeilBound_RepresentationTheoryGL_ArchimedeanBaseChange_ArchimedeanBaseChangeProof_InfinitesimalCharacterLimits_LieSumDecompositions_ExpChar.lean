-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_ExpChar
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_ExpChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:17.160619+00:00
-- url     : https://prove2.me/theorems/d631e8c0-1808-4aeb-bc6d-4f3b983993a7
-- title:
--   Exp Char
-- statement:
--   Definitions and structural lemmas for Exp Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/ExpChar.lean

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
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2
def expChar (c : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (c * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Complex.ofReal_add, mul_add, Complex.exp_add]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2
end


