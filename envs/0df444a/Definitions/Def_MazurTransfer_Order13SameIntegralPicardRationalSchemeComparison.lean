-- Prove2me | Definitions.Def_MazurTransfer_Order13SameIntegralPicardRationalSchemeComparison
-- name    : MazurTransfer_Order13SameIntegralPicardRationalSchemeComparison
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:48:12.431991+00:00
-- url     : https://prove2.me/theorems/7fe1fc90-5eb3-43b5-8c7f-f075ec5d9758
-- title:
--   The actual rational Picard scheme is the rational fibre of the same integral family
-- statement:
--   Let $B=\mathbb Z[1/104]$ and let $D/B$ be the original designated integral Picard family whose canonical mod-3 and mod-5 point sets both have cardinality nineteen. Its actual rational fibre has a representation of the literal rational curve’s rigidified Picard functor. The original actual rational Picard designation $D_{\mathbb Q}^{\mathrm{actual}}$ is canonically isomorphic to that fibre: $$D_{\mathbb Q}^{\mathrm{actual}}\simeq D\times_{\operatorname{Spec}B}\operatorname{Spec}\mathbb Q.$$ The isomorphism is over the rational base, preserves the zero section and respects the canonical internal group laws. It gives multiplicative point equivalences over every rational test scheme. These are the original data used to transport rational diamond and nineteen-norm maps to the same integral family.
-- source:
--   Original complete Order13SameIntegralPicardRationalSchemeComparison.lean from MazurTheorem, Apache-2.0, Vas and contributors. All original declarations, local instance commands and bodies are unchanged; four project imports alone become public interfaces. All thirteen named complete closed types, all nine named construction values and all three local algebra/group instances are kernel-compared with the original environment. Two automatically generated instance names differ in packaging; their actual types and values are checked and recorded as correspondences before comparing the remaining data. The original structural maps, zero sections, canonical rational scalar map and both point-group actions are retained. Reuses the public same-family finite-fibre construction, actual rational Picard designation, original literal-fibre group compatibility and canonical Picard group-scheme comparison. The original official Anthropic FLT APIs retain exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: extension of the actual rational diamond and nineteen-norm morphisms to local integral models and good-prime Kummer conditions.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the SAME actual rational Picard scheme with the
rational fibre of the existing Z[1/104] Picard family by their genuine
representations of the same relative Picard group functor.
Named downstream consumer: extending the actual nineteen norm maps to
local integral models and proving good-prime Kummer conditions.
-/
import Definitions.Def_MazurTransfer_PicardCanonicalRepresentationGroupIsomorphism
import Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRelativeGroupCompatibility_literal_fibre_relative_group_compatibility
import Definitions.Def_MazurTransfer_Order13SameIntegralPicardFamilyFiniteFibres
import Definitions.Def_MazurTransfer_Order13CanonicalRationalScalarMap
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardDesignation

noncomputable section
namespace MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase
open Order13SameIntegralPicardFamilyFiniteFibres
open Order13IntegralPicardLiteralFibreRepresentations
open Order13IntegralPicardLiteralFibreRelativeGroupCompatibility
open Order13ActualPicardDiamondSchemeEndomorphism
open PicardCanonicalRepresentationGroupIsomorphism
open scoped CategoryTheory.MonObj

local instance : Algebra BaseRing ℚ := canonicalRationalMap.toAlgebra

def integralPicard : RelativePic0Designation BaseRing (curveToBase BaseRing) :=
  actual_same_integral_picard_family_finite_fibres.choose

def integralRepresentation : RepresentsRelSubPic (curveToBase BaseRing)
    (positiveInfinitySection BaseRing)
    (algEquivZeroCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)) integralPicard :=
  actual_same_integral_picard_family_finite_fibres.choose_spec.choose

theorem integralPicard_abelian : AbelianSchemePropertyBundle BaseRing integralPicard.toBase :=
  actual_same_integral_picard_family_finite_fibres.choose_spec.choose_spec.1

def rationalFibre := literalFibreDesignation BaseRing ℚ integralPicard

def rationalFibreRepresentation : RepresentsRelSubPic (curveToBase ℚ)
    infinitySection (algEquivZeroCut (curveToBase ℚ) infinitySection) rationalFibre :=
  (literal_fibre_relative_group_compatibility BaseRing ℚ
    integralPicard integralRepresentation).choose

def actualPicardRationalFibreOverIso :
    Over.mk actualPicard.toBase ≅ Over.mk rationalFibre.toBase :=
  canonicalOverIso (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation rationalFibreRepresentation

def actualPicardRationalFibreSchemeIso : actualPicard.P ≅ rationalFibre.P :=
  canonicalSchemeIso (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation rationalFibreRepresentation

theorem actualPicardRationalFibreSchemeIso_over :
    actualPicardRationalFibreSchemeIso.hom ≫ rationalFibre.toBase = actualPicard.toBase :=
  canonicalSchemeIso_over (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation rationalFibreRepresentation

theorem actualPicardRationalFibreSchemeIso_zero :
    actualPicard.zeroSection ≫ actualPicardRationalFibreSchemeIso.hom =
      rationalFibre.zeroSection :=
  canonicalSchemeIso_zero (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation rationalFibreRepresentation

abbrev actualGroup : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition
      actualPicard from actualRepresentation).grpObj

abbrev rationalFibreGroup : GrpObj (Over.mk rationalFibre.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition
      rationalFibre from rationalFibreRepresentation).grpObj

local instance : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance : GrpObj (Over.mk rationalFibre.toBase) := rationalFibreGroup

theorem actualPicardRationalFibreOverIso_isMonHom :
    IsMonHom actualPicardRationalFibreOverIso.hom :=
  canonicalOverIso_isMonHom (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation rationalFibreRepresentation

def actualPicardRationalFibrePointsEquiv (T : Over (Spec (CommRingCat.of ℚ))) :
    (T ⟶ Over.mk actualPicard.toBase) ≃* (T ⟶ Over.mk rationalFibre.toBase) :=
  canonicalPointMulEquiv (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection)
    actualRepresentation rationalFibreRepresentation T

end MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
#print axioms MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.integralPicard_abelian
#print axioms MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualPicardRationalFibreSchemeIso_over
#print axioms MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualPicardRationalFibreSchemeIso_zero
#print axioms MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualPicardRationalFibreOverIso_isMonHom
#print axioms MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualPicardRationalFibrePointsEquiv


