-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:24.350946+00:00
-- url     : https://prove2.me/theorems/a571f45b-f342-4004-aa2d-aa64c9cc7800
-- title:
--   PSep Fac B
-- statement:
--   Definitions and structural lemmas for PSep Fac B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
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
section Comm
variable {B : Type} [CommRing B] [Algebra ℂ B]
end Comm
section Fun
variable {A : Type} [Ring A] [Algebra ℂ A]
end Fun
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
end


