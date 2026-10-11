-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0009
-- name    : PNT_ZeroFree_433_0009
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:05:38.994392+00:00
-- url     : https://prove2.me/theorems/fd3b0389-1562-478f-8cae-7d08ba499a58
-- title:
--   Zero-free region foundations: Arithmetic.EisensteinEmbedding [0009]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L22-L695

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L22-L695
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
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

namespace EisensteinEmbedding

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

noncomputable def ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
noncomputable def pb : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

noncomputable def omega3 : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem omega3_sq : omega3 ^ 2 + omega3 + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by norm_cast
  have hquad : omega3 ^ 2 + omega3 + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold omega3
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  exact hquad

theorem omega3_im : omega3.im = Real.sqrt 3 / 2 := by
  simp [omega3]

theorem omega3_im_ne_zero : omega3.im ≠ 0 := by
  rw [omega3_im]
  exact div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) (by norm_num)

theorem lam_ne_zero (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    1 + 2 * w ≠ 0 := by
  intro h
  have hw' : w = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw'] at hw
  norm_num at hw

theorem pb_minpoly : minpoly ℤ pb.gen =
    (Polynomial.X : Polynomial ℤ) ^ 2 + Polynomial.X + 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hgen : pb.gen = hζ.toInteger := by
    simpa only [pb] using hζ.integralPowerBasis_gen
  rw [hgen]
  calc
    minpoly ℤ (hζ.toInteger : O) =
        minpoly ℤ (hζ.toInteger : K) :=
          (NumberField.RingOfIntegers.minpoly_coe hζ.toInteger).symm
    _ = minpoly ℤ (IsCyclotomicExtension.zeta 3 ℚ K) := by
          exact congrArg (minpoly ℤ) hζ.coe_toInteger
    _ = Polynomial.cyclotomic 3 ℤ :=
          (Polynomial.cyclotomic_eq_minpoly hζ (by decide)).symm
    _ = _ := Polynomial.cyclotomic_three ℤ

noncomputable def embedding (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : O →+* ℂ :=
  (pb.lift w (by
    rw [pb_minpoly]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hw)).toRingHom

theorem embedding_gen (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    embedding w hw pb.gen = w := by
  exact pb.lift_gen w (by
    rw [pb_minpoly]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hw)

theorem pb_dim : pb.dim = 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hdim := hζ.integralPowerBasis_dim
  have htot : Nat.totient 3 = 2 := by decide
  simpa only [pb, htot] using hdim

theorem exists_ab (x : O) : ∃ a b : ℤ, x = a + b * pb.gen := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let c := pb.basis.repr x
  have h := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hi := i.isLt
    have hd := pb_dim
    simp only [i0, i1, Fin.ext_iff]
    omega
  rw [huniv, Finset.sum_insert (by simp [i0, i1]), Finset.sum_singleton] at h
  refine ⟨c i0, c i1, ?_⟩
  simpa only [pb.coe_basis, i0, i1, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, zsmul_eq_mul, mul_one] using h.symm

theorem embedding_apply_ab (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (a b : ℤ) :
    embedding w hw (a + b * pb.gen : O) =
      (a : ℂ) + (b : ℂ) * w := by
  simp only [map_add, map_mul, map_intCast, embedding_gen]

theorem embedding_injective (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (him : w.im ≠ 0) : Function.Injective (embedding w hw) := by
  intro x y hxy
  have hz : embedding w hw (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, b, hrepr⟩ := exists_ab (x - y)
  rw [hrepr, embedding_apply_ab] at hz
  have himz := congrArg Complex.im hz
  have hb : b = 0 := by
    simp only [Complex.add_im, Complex.intCast_im, zero_add,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im] at himz
    have hbc : (b : ℝ) = 0 := (mul_eq_zero.mp himz).resolve_right him
    exact_mod_cast hbc
  have ha : a = 0 := by
    rw [hb, Int.cast_zero, zero_mul, add_zero] at hz
    exact_mod_cast hz
  have hzero : x - y = 0 := by rw [hrepr, ha, hb]; simp
  exact sub_eq_zero.mp hzero

theorem trace_period_on_ringOfIntegers
    (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * w) / lam) = 1) :
    ∀ x : O, ψ (embedding w hw x / lam) = 1 := by
  intro x
  obtain ⟨a, b, hrepr⟩ := exists_ab x
  rw [hrepr, embedding_apply_ab]
  exact hperiod a b

end EisensteinEmbedding

namespace ConcreteTraceCRT

open EisensteinEmbedding IdealGaussCRT

noncomputable def eisEmbedding : O →+* ℂ := embedding omega3 omega3_sq

theorem eisEmbedding_injective : Function.Injective eisEmbedding :=
  embedding_injective omega3 omega3_sq omega3_im_ne_zero

theorem eisEmbedding_ne_zero {a : O} (ha : a ≠ 0) : eisEmbedding a ≠ 0 := by
  intro h
  exact ha (eisEmbedding_injective (by simpa using h))

noncomputable def eisLam : ℂ := 1 + 2 * omega3

theorem eisLam_ne_zero : eisLam ≠ 0 := lam_ne_zero omega3 omega3_sq

theorem eisPeriod (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1) :
    ∀ x : O, ψ (eisEmbedding x / eisLam) = 1 :=
  trace_period_on_ringOfIntegers omega3 omega3_sq ψ eisLam hperiod

def coordinateSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * omega3_sq

theorem coordinateSubring_eq_traceSubring :
    coordinateSubring = ShortDraftTrace.eisensteinSubring := by
  rfl

noncomputable def toCoordinateSubring : O →+* coordinateSubring :=
  eisEmbedding.codRestrict coordinateSubring (by
    intro x
    obtain ⟨a, b, hrepr⟩ := exists_ab x
    rw [hrepr]
    change embedding omega3 omega3_sq (a + b * pb.gen : O) ∈ coordinateSubring
    rw [embedding_apply_ab]
    exact ⟨a, b, rfl⟩)

theorem toCoordinateSubring_injective : Function.Injective toCoordinateSubring := by
  intro x y h
  apply eisEmbedding_injective
  exact congrArg Subtype.val h

theorem toCoordinateSubring_surjective : Function.Surjective toCoordinateSubring := by
  rintro ⟨z, a, b, hz⟩
  refine ⟨(a + b * pb.gen : O), ?_⟩
  apply Subtype.ext
  change eisEmbedding (a + b * pb.gen : O) = z
  change embedding omega3 omega3_sq (a + b * pb.gen : O) = z
  rw [embedding_apply_ab]
  exact hz.symm

noncomputable def ringOfIntegersEquivCoordinateSubring : O ≃+* coordinateSubring :=
  RingEquiv.ofBijective toCoordinateSubring
    ⟨toCoordinateSubring_injective, toCoordinateSubring_surjective⟩

noncomputable def eisTraceModChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a : O) (ha : a ≠ 0) : AddChar (O ⧸ Ideal.span {a}) ℂ :=
  traceModChar eisEmbedding ψ eisLam a
    (eisEmbedding_ne_zero ha) eisLam_ne_zero (eisPeriod ψ hperiod)

noncomputable def eisTraceProdChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0) :
    AddChar (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  traceProdChar eisEmbedding ψ eisLam a b
    (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
    eisLam_ne_zero (eisPeriod ψ hperiod)

theorem gauss_sum_actual_O
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ c d : ℤ,
      ψ (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ψ hperiod a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ψ hperiod a ha) *
      gaussSum χb (eisTraceModChar ψ hperiod b hb) := by
  simpa only [eisTraceProdChar, eisTraceModChar] using
    gauss_sum_trace_crt_of_coprime eisEmbedding ψ eisLam a b hcop
      (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
      eisLam_ne_zero (eisPeriod ψ hperiod) χa χb

theorem finite_quotient_span {a : O} (ha : a ≠ 0) :
    Finite (O ⧸ Ideal.span {a}) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  exact ha (Ideal.span_singleton_eq_bot.mp h)

theorem finite_quotient_product {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  have hab : a * b = 0 := Ideal.span_singleton_eq_bot.mp (by
    simpa only [Ideal.span_singleton_mul_span_singleton] using h)
  exact mul_ne_zero ha hb hab

end ConcreteTraceCRT

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

theorem breveE_period_coordinates :
    ∀ c d : ℤ,
      ShortDraftTrace.breveE
        (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1 := by
  intro c d
  change ShortDraftTrace.breveE
    (((c : ℂ) + (d : ℂ) * ShortDraftTrace.ω₃) /
      (1 + 2 * ShortDraftTrace.ω₃)) = 1
  exact ShortDraftTrace.breveE_period_lam c d

theorem coordinateSubring_eq : coordinateSubring =
    ShortDraftTrace.eisensteinSubring := by
  rfl

noncomputable def ringOfIntegersEquivShortDraftE :
    O ≃+* ShortDraftTrace.eisensteinSubring :=
  coordinateSubring_eq ▸ ringOfIntegersEquivCoordinateSubring

theorem gauss_sum_breveE_actual_O
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
        a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ShortDraftTrace.breveE
        breveE_period_coordinates a ha) *
      gaussSum χb (eisTraceModChar ShortDraftTrace.breveE
        breveE_period_coordinates b hb) := by
  exact gauss_sum_actual_O ShortDraftTrace.breveE
    breveE_period_coordinates a b ha hb hcop χa χb

end ConcreteBreveE

namespace ActualEisensteinCubic

theorem eisEmbedding_conjO (x : O) :
    ConcreteTraceCRT.eisEmbedding (conjO x) =
      star (ConcreteTraceCRT.eisEmbedding x) := by
  let ι := ConcreteTraceCRT.eisEmbedding
  let z := ι omega
  have hz3 : z ^ 3 = 1 := by
    change ι omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ι.comp conjO.toRingHom = (starRingEnd ℂ).comp ι := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ι (conjO omega) = star (ι omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx

theorem cubicGauss_normalized_cube_eis (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    (gaussSum ((cubicChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ψ /
      (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ)) ^ 3 =
      -(ConcreteTraceCRT.eisEmbedding p) /
        (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ) := by
  let z := ConcreteTraceCRT.eisEmbedding p
  let g := gaussSum ((cubicChar P hgood).ringHomComp
    ConcreteTraceCRT.eisEmbedding) ψ
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ConcreteTraceCRT.eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact hqne hq
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube ConcreteTraceCRT.eisEmbedding
      ConcreteTraceCRT.eisEmbedding_injective P hgood p hP hprimary ψ hψ
  change (g / (‖z‖ : ℂ)) ^ 3 = -z / (‖z‖ : ℂ)
  rw [div_pow, hg, hq]
  field_simp

open AddChar MulChar

private theorem sextic_complex_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    ((sexticChar P hgood).ringHomComp ringComplex) ^ j ≠ 1 := by
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff ringComplex_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]

theorem sextic_local_fourier_nonzero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (h : O ⧸ P) (hh : h ≠ 0) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ j) y * ψ (-h * y)) =
    ((((sexticChar P hgood).ringHomComp ringComplex) ^ j) h)⁻¹ *
      gaussSum (((sexticChar P hgood).ringHomComp ringComplex) ^ j)
        (ψ.mulShift (-1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := ((sexticChar P hgood).ringHomComp ringComplex) ^ j
  have hχ : χ ≠ 1 := sextic_complex_pow_ne_one P hgood hchar hj0 hj6
  have ht := ShortDraftFiniteGaussFourier.gauss_transform χ (ψ.mulShift (-1)) hχ h
  rw [if_neg hh] at ht
  simpa only [χ, AddChar.mulShift_apply, neg_one_mul, mul_assoc,
    neg_mul, one_mul] using ht

theorem sextic_local_fourier_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ j) y * ψ (-(0 : O ⧸ P) * y)) =
    0 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := ((sexticChar P hgood).ringHomComp ringComplex) ^ j
  have hχ : χ ≠ 1 := sextic_complex_pow_ne_one P hgood hchar hj0 hj6
  simpa only [χ, neg_zero, zero_mul, map_zero_eq_one, mul_one] using
    MulChar.sum_eq_zero_of_ne_one hχ

theorem sextic_local_fourier_jzero_nonzero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (hψ : ψ.IsPrimitive) (h : O ⧸ P) (hh : h ≠ 0) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y * ψ (-h * y)) =
      -1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hneg : -h ≠ 0 := neg_ne_zero.mpr hh
  have hnon : ψ.mulShift (-h) ≠ 1 := hψ hneg
  have ht := gaussSum_one_left hnon
  simpa only [pow_zero, gaussSum, AddChar.mulShift_apply] using ht

theorem sextic_local_fourier_jzero_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y *
        ψ (-(0 : O ⧸ P) * y)) = (Nat.card (O ⧸ P) : ℂ) - 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hsum := MulChar.sum_one_eq_card_units (R := O ⧸ P) (R' := ℂ)
  have hcard : (Fintype.card (O ⧸ P) : ℂ) =
      (Fintype.card (O ⧸ P)ˣ : ℂ) + 1 := by
    exact_mod_cast (Fintype.card_eq_card_units_add_one (α := O ⧸ P))
  simpa only [pow_zero, neg_zero, zero_mul, map_zero_eq_one, mul_one,
    Nat.card_eq_fintype_card, hcard, add_sub_cancel_right] using hsum

open AddChar MulChar

noncomputable def canonicalSextic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) ℂ :=
  (sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding

theorem canonicalSextic_pow_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : canonicalSextic P hgood ^ 6 = 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ 6 = 1
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.2,
    MulChar.ringHomComp_one]

theorem canonicalSextic_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    canonicalSextic P hgood ^ j ≠ 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ j ≠ 1
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff
    ConcreteTraceCRT.eisEmbedding_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]

theorem canonical_A5_jone (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row
    (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (canonicalSextic_pow_ne_one P hgood hchar (by decide : (3:ℕ) ≠ 0)
      (by decide : (3:ℕ) < 6)) σ ε x

theorem canonical_A5_jfour (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (∑ h : (O ⧸ P)ˣ,
          (((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [ShortDraftLocal.nontrivial_fourier_coefficient (χ ^ 4) ψ hχ4 h,
      map_mul]
    simp only [inv_pow, MulChar.mul_apply]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.sextic_fourth_mask χ ψ hχ6 hψ (ε * x)]
  ring

theorem canonical_A5_jzero_active (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (2:ℕ) ≠ 0) (by decide : (2:ℕ) < 6)
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
        (∑ h : (O ⧸ P)ˣ,
          ((χ⁻¹) ^ 2) (h : O ⧸ P) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hh : (h : O ⧸ P) ≠ 0 := Units.ne_zero h
    rw [pow_zero, ShortDraftLocal.trivial_fourier_coefficient ψ hψ h,
      if_neg hh, map_mul]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.active_zero_local_row χ ψ hχ2 ε x]
  ring

end ActualEisensteinCubic

namespace PrimitiveTrace

open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT

private theorem complex_exp_trace_integer {t : ℂ}
    (ht : Complex.exp (2 * Real.pi * Complex.I * t) = 1) :
    ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ht
  refine ⟨n, ?_⟩
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) Complex.I_ne_zero
  apply mul_left_cancel₀ hnonzero
  calc
    (2 * Real.pi * Complex.I : ℂ) * t = n * (2 * Real.pi * Complex.I) := by
      simpa only [mul_assoc] using hn
    _ = (2 * Real.pi * Complex.I : ℂ) * n := by ring

private theorem phase_integer {z : ℂ}
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1) :
    ∃ n : ℤ, z / eisLam + conj (z / eisLam) = n := by
  apply complex_exp_trace_integer
  exact hz

private theorem omega_conj : conj omega3 = omega3 ^ 2 := by
  have hs : omega3 ^ 2 = -omega3 - 1 := by
    linear_combination omega3_sq
  rw [hs]
  unfold omega3
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private theorem reconstruction (z : ℂ) :
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := by
  have hquad := omega3_sq
  have hl : eisLam ≠ 0 := eisLam_ne_zero
  have hcl : conj eisLam = -eisLam := by
    simp only [eisLam, map_add, map_one, map_mul, map_ofNat, omega_conj]
    linear_combination 2 * hquad
  simp only [map_div₀, map_mul, omega_conj, hcl, div_neg]
  dsimp [eisLam] at *
  field_simp
  linear_combination (conj z) * hquad

private theorem in_coordinate_lattice_of_two_phases (z : ℂ)
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by
  obtain ⟨b, hb⟩ := phase_integer hz
  obtain ⟨c, hc⟩ := phase_integer hwz
  change ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3
  refine ⟨b + c, b, ?_⟩
  calc
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := reconstruction z
    _ = ((b + c : ℤ) : ℂ) + (b : ℂ) * omega3 := by
      rw [hb, hc]
      push_cast
      ring

theorem eisTraceModChar_breveE_ne_one
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp ≠ 1 := by
  intro hψ
  let ι := eisEmbedding
  let z : ℂ := (ι p)⁻¹
  have hpι : ι p ≠ 0 := eisEmbedding_ne_zero hp
  have hbase1 : ∀ x : O,
      ShortDraftTrace.breveE (ι x / (ι p * eisLam)) = 1 := by
    intro x
    have hpoint := congrArg
      (fun f : AddChar (O ⧸ Ideal.span {p}) ℂ =>
        f (Ideal.Quotient.mk (Ideal.span {p}) x)) hψ
    simpa only [eisTraceModChar, IdealGaussCRT.traceModChar_mk,
      AddChar.one_apply] using hpoint
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert! hbase1 1 using 1 ; dsimp [z, ι] ; simp ; field_simp
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert! hbase1 pb.gen using 1
    · rw [show ι pb.gen = omega3 from embedding_gen omega3 omega3_sq]
      dsimp [z]
      field_simp
  have hz := in_coordinate_lattice_of_two_phases z h1 hw
  obtain ⟨q, hq⟩ := toCoordinateSubring_surjective ⟨z, hz⟩
  have hιq : ι q = z := congrArg Subtype.val hq
  have hpq : p * q = 1 := by
    apply eisEmbedding_injective
    rw [map_mul, map_one, hιq]
    dsimp [z]
    exact mul_inv_cancel₀ hpι
  have hunit : IsUnit p := isUnit_iff_dvd_one.mpr ⟨q, hpq.symm⟩
  have htop : P = ⊤ := by
    rw [hP]
    exact Ideal.span_singleton_eq_top.mpr hunit
  exact (inferInstance : P.IsMaximal).ne_top htop

theorem eisTraceModChar_breveE_primitive
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp).IsPrimitive := by
  have : (Ideal.span {p}).IsMaximal := hP ▸ inferInstance
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  exact AddChar.IsPrimitive.of_ne_one
    (eisTraceModChar_breveE_ne_one P p hP hp)

end PrimitiveTrace

end

end OAI

end


