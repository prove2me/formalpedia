-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0044
-- name    : PNT_ZeroFree_433_0044
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:26:10.997391+00:00
-- url     : https://prove2.me/theorems/1fa8c2e0-44a4-41a8-be71-29d402116303
-- title:
--   Zero-free region foundations: GaussSum.CubicTrace [0044]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/CubicTrace.lean#L68-L674

import Definitions.Def_PNT_ZeroFree_433_0041

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/CubicTrace.lean#L68-L674
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
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

namespace ActualEisensteinCubic

theorem cubicChar_reduce_ne_one (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q) :
    (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q) ≠ 1 := by
  intro hred
  apply cubicChar_ne_one P hPgood
  apply MulChar.ext
  intro u
  apply cubic_roots_reduce_injective Q hQgood
  · rw [← (cubicChar P hPgood).pow_apply_coe, cubicChar_pow_three]
    exact MulChar.one_apply_coe u
  · simp
  · have h := congrArg (fun χ : MulChar (O ⧸ P) (O ⧸ Q) => χ (u : O ⧸ P)) hred
    simpa only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one] using h

theorem cubicGauss_cube_of_nontrivial {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (hξ : (cubicChar P hgood).ringHomComp ι ≠ 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hξ3 : ξ ^ 3 = 1 := by
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
  have hξ2 : ξ * ξ ≠ 1 := by
    intro h2
    apply hξ
    calc
      ξ = ξ * (ξ * ξ) := by rw [h2, mul_one]
      _ = ξ ^ 3 := by rw [pow_succ, pow_two]; ac_rfl
      _ = 1 := hξ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hξ3
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hξneg : ξ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hξ3
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξ hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary, map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

theorem cubicGauss_cube_reduce {E : Type*} [Field E]
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (η : (O ⧸ Q) →+* E) (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hPgood).ringHomComp (η.comp (Ideal.Quotient.mk Q))) ψ ^ 3 =
      -(η (Ideal.Quotient.mk Q p)) * (Nat.card (O ⧸ P) : E) := by
  apply cubicGauss_cube_of_nontrivial _ P hPgood p hP hprimary _ ψ hψ
  have h := (MulChar.ringHomComp_ne_one_iff η.injective).mpr
    (cubicChar_reduce_ne_one P Q hPgood hQgood)
  exact h

end ActualEisensteinCubic

namespace CubicFrobenius

theorem card_cast_ne_zero (F F' : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] (hchar : ringChar F' ≠ ringChar F) :
    (Fintype.card F : F') ≠ 0 := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [hcard, Nat.cast_pow]
  apply pow_ne_zero
  intro hz
  have hd := (CharP.cast_eq_zero_iff F' (ringChar F') (ringChar F)).mp hz
  exact hchar ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F' _) hp).mp hd)

theorem gaussSum_pow_card (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (χ : MulChar F F') (ψ : AddChar F E) :
    gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' E))
        (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F' (ringChar F')
  have hchar := Algebra.ringChar_eq F' E
  have hpE : (ringChar E).Prime := hchar ▸ hp
  let : Fact (ringChar E).Prime := ⟨hpE⟩
  have hcardE : Fintype.card F' = ringChar E ^ (n : ℕ) := by simpa only [hchar] using hcard
  unfold gaussSum
  rw [hcardE, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← hcardE]
  change (algebraMap F' E (χ x)) ^ Fintype.card F' * ψ x ^ Fintype.card F' = _
  rw [← map_pow, FiniteField.pow_card, ← AddChar.mulShift_spec']
  rfl

theorem gauss_cube_residue_relation (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (hchar : ringChar F' ≠ ringChar F)
    (χ : MulChar F F') (hχ : χ ≠ 1) (ψ : AddChar F E) (hψ : ψ.IsPrimitive)
    (a : F') (m : ℕ) (hm : Fintype.card F' = 3 * m + 1)
    (hcube : gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ 3 = algebraMap F' E a) :
    χ (Fintype.card F' : F) * a ^ m = 1 := by
  let ξ := χ.ringHomComp (algebraMap F' E)
  have hξ : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (algebraMap F' E).injective).mpr hχ
  have hcard : (Fintype.card F : E) ≠ 0 := by
    rw [← map_natCast (algebraMap F' E)]
    exact (map_ne_zero (algebraMap F' E)).mpr (card_cast_ne_zero F F' hchar)
  have hg : gaussSum ξ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hξ hψ
  have hq : (Fintype.card F' : F) ≠ 0 := card_cast_ne_zero F' F hchar.symm
  let u : Fˣ := (isUnit_iff_ne_zero.mpr hq).unit
  have hu : (u : F) = Fintype.card F' := (isUnit_iff_ne_zero.mpr hq).unit_spec
  have hshift := gaussSum_mulShift ξ ψ u
  rw [hu, ← gaussSum_pow_card F F' E χ ψ] at hshift
  have hp : gaussSum ξ ψ ^ Fintype.card F' =
      algebraMap F' E (a ^ m) * gaussSum ξ ψ := by
    rw [hm, pow_succ, pow_mul, hcube, map_pow]
  rw [hp] at hshift
  have hone : ξ (Fintype.card F' : F) * algebraMap F' E (a ^ m) = 1 := by
    apply mul_right_cancel₀ hg
    simpa only [mul_assoc, one_mul] using hshift
  apply (algebraMap F' E).injective
  simpa only [ξ, map_mul, map_one, MulChar.ringHomComp_apply] using hone

end CubicFrobenius

namespace ActualEisensteinCubic

theorem cubic_primary_frobenius_relation (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O))) = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Field (O ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fintype (O ⧸ Q) := Fintype.ofFinite _
  let ψ := AddChar.FiniteField.primitiveChar (O ⧸ P) (O ⧸ Q) hchar
  let E := CyclotomicField ψ.n (O ⧸ Q)
  let η : (O ⧸ Q) →+* E := algebraMap (O ⧸ Q) E
  let χ := (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q)
  let a : O ⧸ Q := -(Ideal.Quotient.mk Q p) * (Fintype.card (O ⧸ P) : O ⧸ Q)
  let m := (Fintype.card (O ⧸ Q) - 1) / 3
  have hqdiv : 3 ∣ Fintype.card (O ⧸ Q) - 1 := by
    simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three Q hQgood
  have hqpos : 0 < Fintype.card (O ⧸ Q) := Fintype.card_pos
  have hm : Fintype.card (O ⧸ Q) = 3 * m + 1 := by
    dsimp [m]
    omega
  have hcube : gaussSum (χ.ringHomComp η) ψ.char ^ 3 = η a := by
    have hc := cubicGauss_cube_reduce P Q hPgood hQgood p hP hprimary η ψ.char ψ.prim
    convert! hc using 1 <;>
      simp only [a, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card]
  have hrel := CubicFrobenius.gauss_cube_residue_relation (O ⧸ P) (O ⧸ Q) E
    hchar χ (cubicChar_reduce_ne_one P Q hPgood hQgood) ψ.char ψ.prim a m hm hcube
  have heuler := cubicChar_reduce Q hQgood
    (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))
  have heuler' : Ideal.Quotient.mk Q
      (cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = a ^ m := by
    simpa only [a, m, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card] using heuler
  rw [← heuler'] at hrel
  change Ideal.Quotient.mk Q (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) *
    Ideal.Quotient.mk Q (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = 1 at hrel
  have hx : (Fintype.card (O ⧸ Q) : O ⧸ P) ≠ 0 :=
    CubicFrobenius.card_cast_ne_zero (O ⧸ Q) (O ⧸ P) hchar.symm
  have hy : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) ≠ 0 := by
    intro hz
    rw [hz, MulChar.map_zero, map_zero, mul_zero] at hrel
    exact zero_ne_one hrel
  have hxcube : (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  have hycube : (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)
  have hprod : cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O))) = 1 := by
    apply cubic_roots_reduce_injective Q hQgood
    · rw [mul_pow, hxcube, hycube, mul_one]
    · simp
    · simpa only [map_mul, map_one] using hrel
  have hminus : cubicChar Q hQgood (-1 : O ⧸ Q) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (cubicChar_pow_three Q hQgood)
  have hneg : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) =
      (-1) * Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O)) := by
    simp only [map_mul, map_neg, map_natCast]
    ring
  rw [hneg, map_mul, hminus, one_mul] at hprod
  simpa only [Nat.card_eq_fintype_card] using hprod

theorem cubic_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  have hPQ := cubic_primary_frobenius_relation P Q hPgood hQgood hchar p hP hpprimary
  have hQP := cubic_primary_frobenius_relation Q P hQgood hPgood hchar.symm q hQ hqprimary
  simp only [map_mul, map_natCast] at hPQ hQP
  let U := cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P)
  let V := cubicChar Q hQgood (Nat.card (O ⧸ P) : O ⧸ Q)
  have hB : cubicChar Q hQgood (Ideal.Quotient.mk Q p) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hPQ
  have hA : cubicChar P hPgood (Ideal.Quotient.mk P q) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hQP
  have hUV : U * V ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hA
    exact zero_ne_one hA
  exact mul_right_cancel₀ hUV (hA.trans hB.symm)

theorem canonicalSextic_sq_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
    p q hP hQ hpprimary hqprimary]

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem norm_eisEmbedding_unit (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

@[simp] theorem norm_eisEmbedding_unit_mul (u : Oˣ) (a : O) :
    ‖eisEmbedding ((u : O) * a)‖ = ‖eisEmbedding a‖ := by
  rw [map_mul, norm_mul, norm_eisEmbedding_unit, one_mul]

theorem finiteSexticRow_unit_mul_star {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (u : Oˣ) :
    finiteSexticRow P hgood j (u : O) * star (finiteSexticRow P hgood j (u : O)) = 1 := by
  unfold finiteSexticRow
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk (P i)))

def principalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) /
      (‖eisEmbedding c‖ : ℂ)

theorem canonicalNormalizedGauss_eq_principal {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j =
      principalNormalizedGauss P hcop hgood j (finitePrimeModulus P)
        (span_finitePrimeModulus P) (finitePrimeModulus_ne_zero P) := rfl

theorem principal_gauss_sum_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n)
    [Fintype (O ⧸ Ideal.span {c})] [Fintype (O ⧸ Ideal.span {n})] :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) =
      finiteSexticRow P hgood j (u : O) *
        ∑ r : O ⧸ Ideal.span {n}, principalSexticRow P hcop hgood j n hn r *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0 r := by
  let e₀ := Ideal.quotEquivOfEq (hn.trans hc.symm)
  let ū : (O ⧸ Ideal.span {n})ˣ := Units.map (Ideal.Quotient.mk (Ideal.span {n})).toMonoidHom u
  let e : (O ⧸ Ideal.span {n}) ≃ (O ⧸ Ideal.span {c}) := ū.mulLeft.trans e₀.toEquiv
  have he (a : O) : e (Ideal.Quotient.mk (Ideal.span {n}) a) =
      Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a) := by
    change e₀ (Ideal.Quotient.mk (Ideal.span {n}) (u : O) *
      Ideal.Quotient.mk (Ideal.span {n}) a) = _
    rw [← map_mul, Ideal.quotEquivOfEq_mk]
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he, principalSexticRow_mk, principalSexticRow_mk, finiteSexticRow_mul]
  have hphase : eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
      (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a)) =
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0
        (Ideal.Quotient.mk (Ideal.span {n}) a) := by
    rw [eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE, hcn, map_mul, map_mul]
    congr 1
    field_simp [eisEmbedding_ne_zero u.ne_zero]
  rw [hphase]
  ring

theorem principalNormalizedGauss_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n) :
    principalNormalizedGauss P hcop hgood j c hc hc0 =
      finiteSexticRow P hgood j (u : O) *
        principalNormalizedGauss P hcop hgood j n hn hn0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hn0
  let : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  unfold principalNormalizedGauss
  rw [principal_gauss_sum_unit_change P hcop hgood j c n hc hn hc0 hn0 u hcn]
  rw [hcn, norm_eisEmbedding_unit_mul]
  ring

theorem principalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    principalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j (∏ i, p i)
      (span_finset_prod Finset.univ p) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) =
      canonicalProductGauss p hp hcop hgood j := rfl

theorem exists_modulus_unit {ι : Type*} [Fintype ι] (p : ι → O) :
    ∃ u : Oˣ, finitePrimeModulus (fun i => Ideal.span {p i}) = (u : O) * ∏ i, p i := by
  have hs : Ideal.span {∏ i, p i} =
      Ideal.span {finitePrimeModulus (fun i => Ideal.span {p i})} := by
    rw [span_finitePrimeModulus, span_finset_prod]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def modulusUnit {ι : Type*} [Fintype ι] (p : ι → O) : Oˣ :=
  Classical.choose (exists_modulus_unit p)

theorem modulusUnit_spec {ι : Type*} [Fintype ι] (p : ι → O) :
    finitePrimeModulus (fun i => Ideal.span {p i}) = (modulusUnit p : O) * ∏ i, p i :=
  Classical.choose_spec (exists_modulus_unit p)

theorem canonicalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j =
      finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
        canonicalProductGauss p hp hcop hgood j := by
  rw [canonicalNormalizedGauss_eq_principal,
    principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hgood j
      (finitePrimeModulus (fun i => Ideal.span {p i})) (∏ i, p i)
      (span_finitePrimeModulus _) (span_finset_prod Finset.univ p)
      (finitePrimeModulus_ne_zero _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (modulusUnit p) (modulusUnit_spec p), principalNormalizedGauss_eq_product]

theorem canonicalNormalizedGauss_frequency_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (h : O) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j ((modulusUnit p : O) * h)) =
      canonicalProductGauss p hp hcop hgood j *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood j,
    finiteSexticRow_mul, star_mul]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O))) *
        (canonicalProductGauss p hp hcop hgood j *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h)) := by ring
    _ = _ := by rw [finiteSexticRow_unit_mul_star, one_mul]

theorem gauss_weighted_radial_sum_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
        F (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F (‖eisEmbedding h‖ ^ 2)) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  calc
    _ = ∑' h : O, canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        (star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j
          ((modulusUnit p : O) * h)) * F (‖eisEmbedding ((modulusUnit p : O) * h)‖ ^ 2)) :=
      ((modulusUnit p).mulLeft.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [norm_eisEmbedding_unit_mul, ← mul_assoc,
        canonicalNormalizedGauss_frequency_transport p hp hcop hgood j, mul_assoc]

theorem gauss_weighted_finite_radial_sum_transport {ι κ : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (D : Finset κ) (a : κ → ℂ) (F : κ → ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑ k ∈ D, a k * ∑' h : O,
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑ k ∈ D, a k * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            F k (‖eisEmbedding h‖ ^ 2)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a k * (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [gauss_weighted_radial_sum_transport p hp hcop hgood j]; ring

theorem finitePrimeModulus_norm_eq_product {ι : Type*} [Fintype ι] (p : ι → O) :
    ‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖ =
      ‖eisEmbedding (∏ i, p i)‖ := by
  rw [modulusUnit_spec p, norm_eisEmbedding_unit_mul]

theorem canonical_radial_poisson_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow (fun i => Ideal.span {p i}) hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalProductGauss p hp hcop hgood j /
        (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2) := by
  have h := canonical_radial_poisson_normalized (fun i => Ideal.span {p i})
    hcop hgood hchar j hj0 hj6 W scale hscale
  dsimp only at h
  rw [finitePrimeModulus_norm_eq_product p] at h
  rw [h]
  have ht := gauss_weighted_radial_sum_transport p hp hcop hgood j
    (fun t => paperRadialFourier W (scale * t / ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
          ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            paperRadialFourier W
              (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring

theorem moebius_star_canonicalNormalizedGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1)) =
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood (fun _ => 1), star_mul]
  calc
    _ = star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1))) := by ring
    _ = _ := by rw [moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary]

theorem moebius_gauss_frequency_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (h : O) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1) *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1)
          ((modulusUnit p : O) * h))) =
      (star (canonicalProductG p hp hcop hgood))⁻¹ *
        star (canonicalProductCoefficient p hp hcop hgood) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) h) := by
  rw [canonicalNormalizedGauss_frequency_transport p hp hcop hgood (fun _ => 1)]
  have hc := congrArg (fun z : ℂ => star z)
    (moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary)
  simp only [star_mul, star_star, star_inv₀, star_intCast] at hc
  calc
    _ = (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
        (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)) *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) h) := by ring
    _ = _ := by rw [hc]; ring

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

def squarefreePairProductPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i, q i
  ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
      (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem squarefreePairPoissonKernel_eq_product
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let hg : ∀ i : activeSupport S T, lambda ∉ Q i := fun i => hgood i.val
  let j := activeExponent S T
  let row := finiteSexticRow Q hg j
  let n := ∏ i, q i
  let a : Finset ι → ℂ := fun E =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F : Finset ι → ℝ → ℂ := fun E t =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (scale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hc : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    finitePrimeModulus_norm_eq_product q
  unfold squarefreePairPoissonKernel squarefreePairProductPoissonKernel
  dsimp only
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j /
      (‖eisEmbedding (finitePrimeModulus Q)‖ : ℂ)) * _ = _
  rw [hc]
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2)) =
    ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ hg j /
      (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))
  have ht := gauss_weighted_finite_radial_sum_transport q (fun i => hp i.val)
    hQ hg j (S ∩ T).powerset a F
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ hg j *
          (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))) := by ring
    _ = _ := by rw [ht]; ring

theorem finiteSquarefreeRow_pair_radial_poisson_product
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood S z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood T z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  rw [finiteSquarefreeRow_pair_radial_poisson (fun i => Ideal.span {p i}) hinj hgood hchar
    S T W scale hscale, squarefreePairPoissonKernel_eq_product p hp hinj hgood]

end GaussGeneratorTransport

end

end OAI

end


