-- Prove2me | Definitions.Def_MazurTransfer_OriginalLocalRationalSubringEquivalenceData20261020
-- name    : MazurTransfer_OriginalLocalRationalSubringEquivalenceData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T02:05:17.331966+00:00
-- url     : https://prove2.me/theorems/322e598a-8e87-4877-b272-80b8a305d692
-- title:
--   Original local rational-subring coefficient equivalence
-- statement:
--   Retain the exact original localization-to-rational-subring algebra equivalence and its same original localization provider. The complete original constructor type and whole value, original scoped provider type, sixteen context types, six whole context values and all generated certificates are independently checked. Embedding compatibility is a separate theorem interface. The complete existing official FLT localization proof has its exact fresh public type and rational-subring whole value checked independently. Named downstream consumer: classification of the same selected actual integral nineteen character quotient.
-- source:
--   MazurTheorem Order13LocalRationalSubringEquivalence by Vas and contributors; exact original constructor and scoped provider, retaining the Apache-2.0 attribution of the exact official Anthropic FLT localization input.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the EXISTING localization coefficient ring
with the rational-subring coefficient ring in the complete FLT Hopf
classification, proving compatibility with the SAME rational embedding.
Named downstream consumer: actual selected character quotient classification
at nineteen; no definitional identification of base rings is assumed.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt

noncomputable section
namespace MazurTransfer.Order13LocalRationalSubringEquivalence
open Order13LocalIntegralCoefficientMaps
variable (q : ℕ) [Fact q.Prime]

local instance instAtPrimeIntSubtypeRatMemSubringRatLocalizedAtPrimeIdeal_order13LocalRationalSubringEquivalence : IsLocalization.AtPrime (GaloisRep.ratLocalizedAt q) (primeIdeal q) :=
  GaloisRep.isLocalization_ratLocalizedAt (Fact.out : q.Prime)

def localRationalSubringEquiv : LocalRing q ≃ₐ[ℤ] GaloisRep.ratLocalizedAt q :=
  IsLocalization.algEquiv (primeIdeal q).primeCompl (LocalRing q) (GaloisRep.ratLocalizedAt q)







variable (K : Type) [CommRing K] [Algebra ℚ K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
variable [Algebra (GaloisRep.ratLocalizedAt q) K]
variable [IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K]





end MazurTransfer.Order13LocalRationalSubringEquivalence

#print axioms MazurTransfer.Order13LocalRationalSubringEquivalence.localRationalSubringEquiv
#print axioms MazurTransfer.Order13LocalRationalSubringEquivalence.instAtPrimeIntSubtypeRatMemSubringRatLocalizedAtPrimeIdeal_order13LocalRationalSubringEquivalence


