-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
-- name    : MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T08:22:21.530975+00:00
-- url     : https://prove2.me/theorems/0377c5e2-66fd-4fed-b6a5-298edada5af5
-- title:
--   The chosen actual dyadic Picard Neron model
-- statement:
--   One chosen original represented dyadic Picard scheme, its chosen representation and relative law, with the original abelian-scheme and Neron-model properties. The complete original chosen constructor values are retained. Named downstream consumer: actual rational norm extensions on this same scheme.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: select ONE actual represented dyadic mixed Picard scheme
and prove its original abelian-scheme and Neron-model properties over Z_(2).
Named downstream consumer: unique extensions of the actual rational norm
maps after identifying this SAME scheme's pointed rational Picard fibre.
-/
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_abelian_picard_family_and_all_base_changes
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle

noncomputable section
namespace MazurTransfer.Order13ActualDyadicMixedPicardNeronModel
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs
local instance originalDyadicChosenPicardNeronPrimeProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩

def dyadicPicard : RelativePic0Designation BaseRing (curveToBase BaseRing) :=
  (MazurTransfer.order13_actual_dyadic_abelian_picard_family_and_all_base_changes.2).choose

def dyadicRepresentation : RepresentsRelSubPic (curveToBase BaseRing) zeroSection
    (algEquivZeroCut (curveToBase BaseRing) zeroSection) dyadicPicard :=
  (MazurTransfer.order13_actual_dyadic_abelian_picard_family_and_all_base_changes.2).choose_spec.choose

theorem dyadicPicard_abelian : AbelianSchemePropertyBundle BaseRing dyadicPicard.toBase := by
  obtain ⟨L,aj,hb,-⟩ := (MazurTransfer.order13_actual_dyadic_abelian_picard_family_and_all_base_changes.2).choose_spec.choose_spec
  exact hb

def dyadicLaw : RelativeGroupLaw BaseRing dyadicPicard.toBase :=
  (show RepresentsRelSubPic (curveToBase BaseRing) zeroSection
    (algEquivZeroGroupCut (curveToBase BaseRing) zeroSection).toSubPicCondition
      dyadicPicard from dyadicRepresentation).relativeGroupLaw

theorem dyadicPicard_neron : NeronModelPropertyBundle BaseRing ℚ dyadicPicard.toBase :=
  NeronModelPropertyBundle.of_abelianSchemePropertyBundle BaseRing ℚ dyadicPicard_abelian

end MazurTransfer.Order13ActualDyadicMixedPicardNeronModel
#print axioms MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.dyadicRepresentation
#print axioms MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.dyadicPicard_abelian
#print axioms MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.dyadicPicard_neron


