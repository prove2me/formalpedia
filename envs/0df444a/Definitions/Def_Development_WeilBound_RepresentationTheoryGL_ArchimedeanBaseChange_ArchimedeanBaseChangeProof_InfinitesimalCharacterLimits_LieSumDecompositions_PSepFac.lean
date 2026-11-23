-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:29.798796+00:00
-- url     : https://prove2.me/theorems/5b3b62b1-a457-42f0-a742-d22c83f7fbff
-- title:
--   PSep Fac
-- statement:
--   Definitions and structural lemmas for PSep Fac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean

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
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
section Ring
variable {A : Type} [Ring A] [Algebra ℂ A]
def IsSS (x : A) : Prop := ∃ s : Finset ℂ, aeval x (∏ v ∈ s, (X - C v)) = 0
end Ring
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
end


