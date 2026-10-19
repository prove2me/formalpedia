-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardModelsData
-- name    : MazurTransfer_Order13GoodPrimeLocalPicardModelsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T04:21:02.343014+00:00
-- url     : https://prove2.me/theorems/9f92037c-811b-4e89-8a9e-0a5ece905ef9
-- title:
--   Good-prime local models of the same integral Picard family
-- statement:
--   Let $q$ be a prime with $q \nmid 104$. Base change the selected integral Picard family of the order-13 curve from $\mathbb Z[1/104]$ to $\mathbb Z_{(q)}$. This interface retains the actual local Picard scheme, its representation of the degree-zero relative Picard functor, and its canonical group law. The local scheme is smooth, proper and geometrically connected, hence is an abelian scheme.
--
--   These constructors supply the same local model used to extend the actual rational norm maps; they introduce no separately chosen Picard scheme.
-- source:
--   MazurTheorem, Order13GoodPrimeLocalPicardModels.lean, complete original declarations (source SHA-256 302ffc9f1d3c07da54c25e06e39419fea856cf6fdc0b5ee4cfc9ba50cc372127), Apache-2.0. Original declaration types and nonproof values checked in full. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pull the SAME selected integral Picard family back to
Z_(q) at every prime not dividing 104, with genuine Picard representations
and proved abelian scheme geometry. Named downstream consumer: local
Neron extension of the actual rational nineteen norm maps.
-/
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13SameIntegralPicardRationalSchemeComparison
import Theorems.Thm_MazurTransfer_Order13EveryRepresentedIntegralPicardGeometry_every_represented_integral_picard_geometry
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps

noncomputable section
namespace MazurTransfer.Order13GoodPrimeLocalPicardModels
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase
open Order13SameIntegralPicardFamilyFiniteFibres Order13LocalIntegralCoefficientMaps
open Order13SameIntegralPicardRationalSchemeComparison
open Order13IntegralPicardLiteralFibreRepresentations
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

include hq in
theorem goodPrime_unit104 : IsUnit (104 : LocalRing q) := by
  have h : (104 : ℤ) ∈ (primeIdeal q).primeCompl := by
    change (104 : ℤ) ∉ Ideal.span {(q : ℤ)}
    rw [Ideal.mem_span_singleton]
    exact hq
  simpa only [map_ofNat] using IsLocalization.map_units (LocalRing q) ⟨104, h⟩

def goodPrimeBaseMap : BaseRing →+* LocalRing q :=
  mapToRing (LocalRing q) (goodPrime_unit104 q hq)

theorem goodPrimeRationalMap_comp :
    (algebraMap (LocalRing q) ℚ).comp (goodPrimeBaseMap q hq) = canonicalRationalMap :=
  mapToRing_natural _ _ _

def localPicard : RelativePic0Designation (LocalRing q) (curveToBase (LocalRing q)) :=
  letI : Algebra BaseRing (LocalRing q) := (goodPrimeBaseMap q hq).toAlgebra
  literalFibreDesignation BaseRing (LocalRing q) integralPicard

def localRepresentation : RepresentsRelSubPic (curveToBase (LocalRing q))
    (positiveInfinitySection (LocalRing q))
    (algEquivZeroCut (curveToBase (LocalRing q)) (positiveInfinitySection (LocalRing q)))
    (localPicard q hq) :=
  letI : Algebra BaseRing (LocalRing q) := (goodPrimeBaseMap q hq).toAlgebra
  (literal_fibre_representation BaseRing (LocalRing q)
    integralPicard integralRepresentation).some

theorem localPicard_geometry :
    Smooth (localPicard q hq).toBase ∧ IsProper (localPicard q hq).toBase ∧
      GeometricallyConnected (localPicard q hq).toBase :=
  Order13EveryRepresentedIntegralPicardGeometry.every_represented_integral_picard_geometry (LocalRing q) (goodPrime_unit104 q hq)
    (localPicard q hq) (localRepresentation q hq)

def localLaw :=
  (show RepresentsRelSubPic (curveToBase (LocalRing q)) (positiveInfinitySection (LocalRing q))
    (algEquivZeroGroupCut (curveToBase (LocalRing q))
      (positiveInfinitySection (LocalRing q))).toSubPicCondition (localPicard q hq)
      from localRepresentation q hq).relativeGroupLaw

theorem localPicard_abelian :
    AbelianSchemePropertyBundle (LocalRing q) (localPicard q hq).toBase := by
  obtain ⟨hs, hp, hg⟩ := localPicard_geometry q hq
  letI := hg
  exact ⟨hs, hp, fun s => (localPicard q hq).toBase.isConnected_preimage_singleton s,
    ⟨localLaw q hq⟩⟩

end MazurTransfer.Order13GoodPrimeLocalPicardModels
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.goodPrime_unit104
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.goodPrimeRationalMap_comp
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.localRepresentation
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.localPicard_abelian

#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.goodPrimeBaseMap
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.localPicard
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.localPicard_geometry
#print axioms MazurTransfer.Order13GoodPrimeLocalPicardModels.localLaw


