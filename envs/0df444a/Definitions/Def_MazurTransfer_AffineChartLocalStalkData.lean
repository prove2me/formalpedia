-- Prove2me | Definitions.Def_MazurTransfer_AffineChartLocalStalkData
-- name    : MazurTransfer_AffineChartLocalStalkData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:32:58.365981+00:00
-- url     : https://prove2.me/theorems/7d9195b6-1cbf-48a7-b3b6-bfc1b63b280c
-- title:
--   The original chart prime and canonical localization-to-stalk isomorphism
-- statement:
--   For the specified affine open chart $j:\operatorname{Spec}A\to X$, each chart point $p$ gives its original prime ideal and the canonical isomorphism $$A_{\mathfrak p}\simeq\mathcal O_{X,j(p)}.$$ These exact constructors supply the chart-coordinate/stalk compatibility theorem and identify the two actual Pell valuation rings with the literal infinity section stalks.
-- source:
--   Original complete chartPrime and localStalkIso declarations and bodies from MazurTheorem AffineOpenChartFunctionFieldStalk.lean, Apache-2.0, Vas and contributors. Two complete original closed types and two data values are kernel-compared. Public imports alone replace the original affine-chart dependency. The design boundary and named consumer are explicit in the checked source. Named downstream consumer: local_stalk_coordinate_commutes and actual infinity section centers.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the chart's generic field isomorphism commutes with the
actual maps from every stalk. Named downstream consumer: identifying the
two Pell valuation rings with the two literal infinity section centers.
-/
/- Design boundary: the original chart prime and local-stalk isomorphism.
Named downstream consumer: the chart-coordinate/stalk commutation theorem. -/
import Definitions.Def_MazurTransfer_AffineOpenChartFunctionField
noncomputable section
universe u
namespace MazurTransfer.AffineOpenChartFunctionFieldStalk
open AlgebraicGeometry CategoryTheory
open AffineOpenChartFunctionField
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

def chartPrime (p : Spec A) : PrimeSpectrum A := p

def localStalkIso (p : Spec A) :
    CommRingCat.of (Localization.AtPrime (chartPrime A p).asIdeal) ≅ X.presheaf.stalk (j p) :=
  (Spec.stalkIso A (chartPrime A p)).symm ≪≫ (asIso (j.stalkMap p)).symm

end MazurTransfer.AffineOpenChartFunctionFieldStalk
#print axioms MazurTransfer.AffineOpenChartFunctionFieldStalk.localStalkIso


