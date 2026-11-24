-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariant
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:56.835819+00:00
-- url     : https://prove2.me/theorems/fc420198-e29f-4402-b30a-14007b469cfb
-- title:
--   Unimodular Haar Right Invariant
-- statement:
--   Definitions and structural lemmas for Unimodular Haar Right Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnimodularHaarRightInvariant.lean

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
namespace GlobalTheory.CompanionTheory.HaarUnimod
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
end GlobalTheory.CompanionTheory.HaarUnimod


