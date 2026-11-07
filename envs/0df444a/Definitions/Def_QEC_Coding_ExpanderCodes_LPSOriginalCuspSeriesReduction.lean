-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:06:25.799281+00:00
-- url     : https://prove2.me/theorems/2fdb86b6-c0d0-4fb6-971f-55cd43383aec
-- title:
--   LPSOriginal Cusp Series Reduction
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cusp Series Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
abbrev lpsOriginalCuspSeriesRing (R : Type*) [CommRing R] : Type _ :=
  Localization.Away (PowerSeries.X : PowerSeries R)
def lpsOriginalCuspCoefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : lpsOriginalCuspSeriesRing R →+* lpsOriginalCuspSeriesRing S :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries R)
    (g:=(algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S)).comp (PowerSeries.map f))
    (by
      change IsUnit (algebraMap (PowerSeries S) (lpsOriginalCuspSeriesRing S)
        (PowerSeries.map f PowerSeries.X))
      rw [PowerSeries.map_X]
      exact IsLocalization.Away.algebraMap_isUnit PowerSeries.X)
def lpsOriginalCyclotomicCuspReduction (p : ℕ) [Fact p.Prime] :
    lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p) →+*
      lpsOriginalCuspSeriesRing (ZMod p) :=
  lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p)
def lpsOriginalCuspJNumerator (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) lpsOriginalJZSeries
def lpsOriginalCuspJWidth (R : Type*) [CommRing R] (m : ℕ) (hm : m≠0) :
    lpsOriginalCuspSeriesRing R :=
  (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
    (PowerSeries.X : PowerSeries R))^m *
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (PowerSeries.expand m hm (lpsOriginalCuspJNumerator R))
def lpsOriginalCyclotomicFiniteCuspBranch (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p) :=
  IsLocalization.Away.invSelf
    (S:=lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p))
    (PowerSeries.X : PowerSeries (lpsOriginalCyclotomicCoefficientRing p)) *
    algebraMap (PowerSeries (lpsOriginalCyclotomicCoefficientRing p))
      (lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p))
      (PowerSeries.C ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^((p-1)*m)) *
        PowerSeries.rescale ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)
          (lpsOriginalCuspJNumerator (lpsOriginalCyclotomicCoefficientRing p)))
def lpsOriginalCyclotomicFormalPrimeProduct (p : ℕ) [Fact p.Prime] :
    Polynomial (lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p)) :=
  (Polynomial.X-Polynomial.C
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) (p*p)
        (Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (Fact.out : p.Prime).ne_zero))) *
    ∏ m : Fin p,
      (Polynomial.X-Polynomial.C (lpsOriginalCyclotomicFiniteCuspBranch p m.val))
def lpsOriginalClearedPolePolynomialSeries {R : Type*} [CommRing R]
    (F : PowerSeries R) (m D : ℕ) (P : Polynomial R) : PowerSeries R :=
  ∑ i ∈ Finset.range (D+1),
    PowerSeries.C (P.coeff i) * PowerSeries.X^(m*(D-i)) * F^i
end
end QEC.Coding.TannerLiftedProduct


