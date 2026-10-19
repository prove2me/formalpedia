-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalChosenRationalPicardComparisonData20261019
-- name    : MazurTransfer_Order13DyadicOriginalChosenRationalPicardComparisonData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T08:29:47.411583+00:00
-- url     : https://prove2.me/theorems/11335388-f1cd-448d-a6a7-eaba6aa74e4b
-- title:
--   The same chosen dyadic rational Picard comparison
-- statement:
--   The original chosen dyadic Picard rational fibre represents the fixed original pointed square curve Picard functor. Its canonical arithmetic comparison lies over the rational base, preserves the original zero and respects the internal group law. The original prime and both original group-object instance names, complete types and whole values are retained. Named downstream consumer: transport and Neron extensions of both actual nineteen norm maps.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME selected dyadic mixed Picard scheme has a rational
fibre representing the fixed square curve's pointed Picard functor. Its
canonical comparison with the fixed arithmetic Picard preserves the zero
and is an internal group morphism through the accepted public contract.
Named downstream consumer: transport of the actual nineteen norm factors
onto this SAME dyadic generic fibre, followed by their Neron extensions.
-/
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
import Definitions.Def_MazurTransfer_Order13MixedOriginalPointedCurveAndLiteralPicardFibreTransportData20261019
import Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
import Definitions.Def_MazurTransfer_PicardCanonicalRepresentationGroupIsomorphism
import Theorems.Thm_MazurTransfer_internal_monoid_morphism_of_all_points

noncomputable section
namespace MazurTransfer.Order13DyadicMixedRationalPicardComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedIntegralSections Order13ActualDyadicMixedPicardNeronModel
open Order13MixedIntegralPicardLiteralFibreRepresentations
open Order13MixedIntegralPicardLiteralFibreRelativeGroupCompatibility
open Order13DyadicMixedRationalPointedCurveComparison
open CurveIsoPicardRepresentationTransport PicardCanonicalRepresentationGroupIsomorphism
open Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
local instance instFactPrimeOfNatNat_order13DyadicMixedRationalPicardComparison : Fact (Nat.Prime 2) := ⟨by decide⟩

def rationalMixedPicard : RelativePic0Designation ℚ (curveToBase ℚ) :=
  literalFibreDesignation BaseRing ℚ dyadicPicard

def rationalMixedRepresentation : RepresentsRelSubPic (curveToBase ℚ)
    (positiveInfinitySection ℚ)
    (algEquivZeroCut (curveToBase ℚ) (positiveInfinitySection ℚ)) rationalMixedPicard :=
  (literal_fibre_relative_group_compatibility BaseRing ℚ dyadicPicard dyadicRepresentation).choose

def rationalPicard : RelativePic0Designation ℚ
    (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) :=
  relabelDesignation (c' := MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) rationalMixedPicard

def rationalRepresentation : RepresentsRelSubPic
    (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
    rationalPicard :=
  transportRepresentation squareToMixedIso squareToMixedIso_over squareToMixedIso_section
    rationalMixedPicard rationalMixedRepresentation

theorem rationalPicard_toBase : rationalPicard.toBase =
    pullback.snd dyadicPicard.toBase (specGenericFibreInclusion BaseRing ℚ) := rfl

def actualDyadicRationalOverIso : Over.mk actualPicard.toBase ≅ Over.mk rationalPicard.toBase :=
  canonicalOverIso (P := algEquivZeroGroupCut
    (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
    actualRepresentation rationalRepresentation

def actualDyadicRationalSchemeIso : actualPicard.P ≅ rationalPicard.P :=
  canonicalSchemeIso (P := algEquivZeroGroupCut
    (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
    actualRepresentation rationalRepresentation

theorem actualDyadicRationalSchemeIso_over :
    actualDyadicRationalSchemeIso.hom ≫ rationalPicard.toBase = actualPicard.toBase :=
  canonicalSchemeIso_over (P := algEquivZeroGroupCut
    (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
    actualRepresentation rationalRepresentation

theorem actualDyadicRationalSchemeIso_zero :
    actualPicard.zeroSection ≫ actualDyadicRationalSchemeIso.hom = rationalPicard.zeroSection :=
  canonicalSchemeIso_zero (P := algEquivZeroGroupCut
    (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
    actualRepresentation rationalRepresentation

abbrev actualGroup : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ)
      infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

abbrev rationalGroup : GrpObj (Over.mk rationalPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ)
      infinitySection).toSubPicCondition rationalPicard from rationalRepresentation).grpObj

local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedRationalPicardComparison : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard : GrpObj (Over.mk rationalPicard.toBase) := rationalGroup

theorem actualDyadicRationalOverIso_isMonHom : IsMonHom actualDyadicRationalOverIso.hom :=
  MazurTransfer.internal_monoid_morphism_of_all_points _
    (canonicalOverIso_points_one (P := algEquivZeroGroupCut
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
      actualRepresentation rationalRepresentation)
    (canonicalOverIso_points_mul (P := algEquivZeroGroupCut
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection)
      actualRepresentation rationalRepresentation)

end MazurTransfer.Order13DyadicMixedRationalPicardComparison
#print axioms MazurTransfer.Order13DyadicMixedRationalPicardComparison.rationalRepresentation
#print axioms MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualDyadicRationalSchemeIso_zero
#print axioms MazurTransfer.Order13DyadicMixedRationalPicardComparison.actualDyadicRationalOverIso_isMonHom


