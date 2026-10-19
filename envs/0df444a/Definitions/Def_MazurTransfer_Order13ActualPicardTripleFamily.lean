-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardTripleFamily
-- name    : MazurTransfer_Order13ActualPicardTripleFamily
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T04:41:14.398671+00:00
-- url     : https://prove2.me/theorems/15fe1b39-e165-4646-8964-a7dae1217d71
-- title:
--   The actual 216 triples of the six marked order-thirteen sections
-- statement:
--   Let $R$ be a commutative ring. Apply the specified indexed triple-family constructor to the actual six marked sections $$\infty^+,\ \infty^-,\ (0,1),\ (0,-1),\ (-1,1),\ (-1,-1)$$ of the actual order-thirteen curve over $R$. This gives the family of $216$ ordered triples used in the integral Picard chart construction. The family is specified over every commutative ring; the theorem that it satisfies the Picard chart-section condition under the good-characteristic hypothesis is separate.
-- source:
--   The unchanged actualTripleFamily constructor from checked MazurTheorem Order13ActualIntegralPicardChartSections.lean. Complete Lean frontend command and declaration ranges retain only the constructor, with direct public imports for the generic triple family and the actual six marked sections. Its complete original kernel type is checked by a closed witness. Per-file attribution and Apache-2.0 are retained. Vas and contributors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: all 216 ordered triples of the six actual marked sections
satisfy the original integral Picard chart-section contract with g=2, r=5.
Named downstream consumer: original-base representation of the degree-zero
Picard subfunctor for the literal order-13 curve.
-/
import Definitions.Def_MazurTransfer_SixSectionTripleFamilyPublic
import Definitions.Def_MazurTransfer_Order13SixMarkedIntegralSections


noncomputable section
universe u
namespace MazurTransfer.Order13ActualIntegralPicardChartSections
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections SixSectionPicardChartCriterion
variable (R : Type u) [CommRing R]

def actualTripleFamily := tripleFamily (curveToBase R) (sixMarkedSections R)
end MazurTransfer.Order13ActualIntegralPicardChartSections
#print axioms MazurTransfer.Order13ActualIntegralPicardChartSections.actualTripleFamily


