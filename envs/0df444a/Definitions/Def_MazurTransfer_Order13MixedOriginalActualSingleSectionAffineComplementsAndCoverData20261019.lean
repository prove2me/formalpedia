-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalActualSingleSectionAffineComplementsAndCoverData20261019
-- name    : MazurTransfer_Order13MixedOriginalActualSingleSectionAffineComplementsAndCoverData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T07:04:41.659716+00:00
-- url     : https://prove2.me/theorems/4895f966-5eb8-4dcf-bdc7-f6e0db3ff775
-- title:
--   Stable original affine-complement and two-affine-cover import interface
-- statement:
--   Stable original affine-complement and two-affine-cover import interface Named downstream consumer: Actual finite-map data on the same whole mixed quadratic curve and original positive infinity section.
-- source:
--   MazurTheorem original mixed quadratic affine complements and finite scheme comparisons, by Vas and contributors; original per-file Apache-2.0 attribution retained. Exact official Anthropic FLT source pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: stable import interface for the original actual affine complements and two-affine cover, using independently checked and cached constructor parts.
Named downstream consumer: actual finite-map data and the dyadic Picard representation.
The original full checked native module is retained as an independently audited equivalent compatibility implementation.
-/
import Definitions.Def_MazurTransfer_Order13MixedOriginalOrdinaryFiniteModelComparisonAndActualTwoAffineCoverCachedPartV320261019
#print axioms MazurTransfer.Order13MixedSingleSectionActualTwoAffineCover.actualTwoAffineOpenCover
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartOpen_isAffineOpen

noncomputable section
universe u
namespace MazurTransfer.ActualAffineComplementCachedImportFacadeOriginalContract20261019
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
/-- Retain the complete original section-complement contract at the stable import boundary. -/
theorem originalCoverComplement (R : Type u) [CommRing R] [IsDomain R] :
    ((Order13MixedSingleSectionActualTwoAffineCover.actualTwoAffineOpenCover R).U1 : Set (curveScheme R)) =
      (Set.range (Order13MixedQuadraticInfinitySections.infinitySectionZero R))ᶜ :=
  Order13MixedSingleSectionActualTwoAffineCover.actualTwoAffineOpenCover_complement R
end MazurTransfer.ActualAffineComplementCachedImportFacadeOriginalContract20261019
end
#print axioms MazurTransfer.ActualAffineComplementCachedImportFacadeOriginalContract20261019.originalCoverComplement


