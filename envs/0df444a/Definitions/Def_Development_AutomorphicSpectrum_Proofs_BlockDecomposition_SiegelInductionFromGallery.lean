-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:46.991654+00:00
-- url     : https://prove2.me/theorems/dd6e1f13-a438-4e24-9993-8134b05fbdd5
-- title:
--   Siegel Induction From Gallery
-- statement:
--   Definitions and structural lemmas for Siegel Induction From Gallery, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
section Heights
variable {G : Type} [Group G] [TopologicalSpace G]
end Heights
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
end GlobalTheory.CompanionTheory.RgEis


