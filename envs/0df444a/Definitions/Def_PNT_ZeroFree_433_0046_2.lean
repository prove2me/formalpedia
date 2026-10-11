-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0046_2
-- name    : PNT_ZeroFree_433_0046_2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:55:52.240619+00:00
-- url     : https://prove2.me/theorems/860a9027-25de-464b-a41a-2f52f23710e3
-- title:
--   Zero-free region foundations: GaussSum.SquarePhaseFactorization [0046_2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean#L321-L451

import Definitions.Def_PNT_ZeroFree_433_0046_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic


theorem cubicTwoIdeal_good : lambda ∉ cubicTwoIdeal := by
  apply primary_maximal_divisor_good (-2 : O) neg_two_primary
  exact Ideal.subset_span (by simp)

theorem cubicTwoIdeal_residue_char : ringChar (O ⧸ cubicTwoIdeal) = 2 := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  have hmem : (2 : O) ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.subset_span (by simp)
  have hz : (2 : O ⧸ cubicTwoIdeal) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ cubicTwoIdeal) _)
    Nat.prime_two).mp ((ringChar.spec (O ⧸ cubicTwoIdeal) 2).mp hz)

theorem canonicalSextic_four_eq_fixed_two
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)) =
      ConcreteTraceCRT.eisEmbedding
        (cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal p)) := by
  have hfour : Ideal.Quotient.mk P (4 : O) = (Ideal.Quotient.mk P (-2 : O)) ^ 2 := by
    simp only [map_ofNat, map_neg]
    ring
  rw [hfour, map_pow, ← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
    canonicalSextic_pow_two]
  change ConcreteTraceCRT.eisEmbedding (cubicChar P hgood (Ideal.Quotient.mk P (-2 : O))) = _
  congr 1
  exact cubic_reciprocity_primary P cubicTwoIdeal hgood cubicTwoIdeal_good
    p (-2) hP rfl hprimary neg_two_primary

theorem canonicalSextic_four_prod_eq_fixed_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) =
      ConcreteTraceCRT.eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
        (Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i))) := by
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_four_eq_fixed_two (P i) (hgood i) (p i) (hP i hi) (hprimary i hi)

theorem canonicalSextic_four_prod_eq_one_of_mod_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hmod : (2 : O) ∣ (∏ i ∈ s, p i) - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) = 1 := by
  have hmem : (∏ i ∈ s, p i) - 1 ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.mem_span_singleton.mpr hmod
  have heq : Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i) = 1 := by
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  rw [canonicalSextic_four_prod_eq_fixed_two s P hgood p hP hprimary, heq, map_one, map_one]

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem sum_square_phase_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) :
    (∑ x : T, ψ (x ^ 2)) =
      ∏ i, ∑ y : R i, coordinateAddChar R e ψ i (y ^ 2) := by
  calc
    _ = ∑ x : T, ∏ i, coordinateAddChar R e ψ i ((e x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (x ^ 2)]
      simp only [map_pow, Pi.pow_apply]
    _ = ∑ x : ∀ i, R i, ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2) :=
      Equiv.sum_comp e.toEquiv
        (fun x : ∀ i, R i => ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2))
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => coordinateAddChar R e ψ i (x ^ 2))).symm

theorem quadratic_gauss_finite_crt_eq_square_sum {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ)
    (hψ : ψ.IsPrimitive) (hchar : ∀ i, ringChar (R i) ≠ 2) :
    (∑ x : T, (∏ i, ((quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : T, ψ (x ^ 2) := by
  rw [gauss_sum_finite_crt R e
    (fun i => (quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) ψ,
    sum_square_phase_finite_crt R e ψ]
  apply Finset.prod_congr rfl
  intro i _
  have hp := coordinateAddChar_isPrimitive R e ψ hψ i
  have hn : coordinateAddChar R e ψ i ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase _ (hchar i) hn

end IdealGaussCRT

namespace QuadraticGaussRay

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem canonicalProductGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticGammaO (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ Ideal.span {p i}) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) hchar


open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates


end QuadraticGaussRay

end

end OAI

end


