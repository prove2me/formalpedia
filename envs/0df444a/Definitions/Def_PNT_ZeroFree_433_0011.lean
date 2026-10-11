-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0011
-- name    : PNT_ZeroFree_433_0011
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:09:07.859186+00:00
-- url     : https://prove2.me/theorems/119eb9a4-1e64-4f16-b314-0bf3cf6af8cb
-- title:
--   Zero-free region foundations: GaussSum.SexticNormalization [0011]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L24-L615

import Definitions.Def_PNT_ZeroFree_433_0010

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L24-L615
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization
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

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveGamma1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

noncomputable def breveGamma3 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 3)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_three_quadratic (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 3 =
      (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ) := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 3 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.1]
  ext x
  change eisEmbedding ((quadraticChar (O ⧸ P) x : ℤ) : O) =
    ((quadraticChar (O ⧸ P) x : ℤ) : ℂ)
  simp

theorem breveGamma1_gamma2_relation (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (canonicalSextic P hgood
        (Ideal.Quotient.mk P (4 : O)))⁻¹ *
      breveGamma3 P hgood p hP hp *
        (breveGamma2 P hgood p hP hp) ^ 3 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (2 : ℕ) ≠ 0) (by decide : (2 : ℕ) < 6)
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (4 : ℕ) ≠ 0) (by decide : (4 : ℕ) < 6)
  have hχ3 : χ ^ 3 = (quadraticChar (O ⧸ Ideal.span {p})).ringHomComp
      (Int.castRingHom ℂ) := canonicalSextic_pow_three_quadratic (Ideal.span {p}) hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hmul := JacobiQuadratic.normalized_gauss_sextic_relation
    χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6 s hs hs0
  have hfour : (4 : O ⧸ Ideal.span {p}) ≠ 0 := by
    have htwo : (2 : O ⧸ Ideal.span {p}) ≠ 0 := Ring.two_ne_zero hchar
    convert! pow_ne_zero 2 htwo using 1 ; norm_num
  have hχfour : χ (4 : O ⧸ Ideal.span {p}) ≠ 0 :=
    χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hfour)
  change χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3 at hmul
  change breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    (χ 4)⁻¹ * breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3
  calc
    breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp =
      (χ 4)⁻¹ * (χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp) := by field_simp
    _ = (χ 4)⁻¹ * (breveGamma3 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3) := by rw [hmul]
    _ = _ := by ring

end

section

open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT

private theorem breveE_period_O (x : O) :
    ShortDraftTrace.breveE (eisEmbedding x) = 1 := by
  obtain ⟨a, b, hx⟩ := exists_ab x
  rw [hx]
  change ShortDraftTrace.breveE
    (embedding omega3 omega3_sq (a + b * pb.gen : O)) = 1
  rw [embedding_apply_ab]
  change ShortDraftTrace.breveE
    ((a : ℂ) + (b : ℂ) * ShortDraftTrace.ω₃) = 1
  exact ShortDraftTrace.breveE_period_integer a b

private noncomputable def eisBreveModChar (p : O) (hp : p ≠ 0) :
    AddChar (O ⧸ Ideal.span {p}) ℂ :=
  traceModChar eisEmbedding ShortDraftTrace.breveE 1 p
    (eisEmbedding_ne_zero hp) one_ne_zero (by
      intro x
      simpa only [div_one] using breveE_period_O x)

theorem eisEmbedding_traceLambda :
    eisEmbedding traceLambda = eisLam := by
  have hgen : pb.gen = omega := by
    simpa only [pb, omega] using
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen
  change embedding omega3 omega3_sq (1 + 2 * omega : O) = 1 + 2 * omega3
  rw [← hgen]
  simp only [map_add, map_one, map_mul, map_ofNat, embedding_gen]

private theorem eisBreveModChar_eq_mulShift (p : O) (hp : p ≠ 0) :
    eisBreveModChar p hp =
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp).mulShift
        (Ideal.Quotient.mk (Ideal.span {p}) traceLambda) := by
  apply DFunLike.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change ShortDraftTrace.breveE (eisEmbedding x / (eisEmbedding p * 1)) =
    ShortDraftTrace.breveE
      (eisEmbedding (traceLambda * x) / (eisEmbedding p * eisLam))
  congr 1
  rw [map_mul, eisEmbedding_traceLambda]
  field_simp [eisEmbedding_ne_zero hp, eisLam_ne_zero]

end

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveLocalG (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)))⁻¹ *
    breveGamma3 P hgood p hP hp

theorem breveGamma1_gamma2_eq_neg_alpha_G (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (-(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ)) *
        breveLocalG P hgood p hP hp := by
  rw [breveGamma1_gamma2_relation P hgood hchar p hP hp hprimary,
    breveGamma2_cube P hgood p hP hp hprimary]
  unfold breveLocalG
  ring

end

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

noncomputable def breveGamma2Product
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b}) : ℂ := by
  letI : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  letI : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let χa := canonicalSextic (Ideal.span {a}) hgooda
  let χb := canonicalSextic (Ideal.span {b}) hgoodb
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (χa ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    (χb ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
      a b ha hb x) / (‖eisEmbedding (a * b)‖ : ℂ)

theorem breveGamma2Product_crt
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b})
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    breveGamma2Product a b ha hb hgooda hgoodb =
      (canonicalSextic (Ideal.span {a}) hgooda
        (Ideal.Quotient.mk (Ideal.span {a}) b)) ^ 2 *
      (canonicalSextic (Ideal.span {b}) hgoodb
        (Ideal.Quotient.mk (Ideal.span {b}) a)) ^ 2 *
      breveGamma2 (Ideal.span {a}) hgooda a rfl ha *
      breveGamma2 (Ideal.span {b}) hgoodb b rfl hb := by
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let χa := canonicalSextic (Ideal.span {a}) hgooda
  let χb := canonicalSextic (Ideal.span {b}) hgoodb
  have hsum := gauss_sum_breveE_actual_O a b ha hb hcop (χa ^ 2) (χb ^ 2)
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) =
      (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul]
    norm_cast
  change (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (χa ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    (χb ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates a b ha hb x) /
      (‖eisEmbedding (a * b)‖ : ℂ) = _
  rw [hsum, hnorm]
  simp only [χa.pow_apply' (by decide : (2 : ℕ) ≠ 0),
    χb.pow_apply' (by decide : (2 : ℕ) ≠ 0)]
  unfold breveGamma2
  ring

end ActualEisensteinCubic

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def normalizedTraceGauss
    (a : O) (ha : a ≠ 0) (χ : MulChar (O ⧸ Ideal.span {a}) ℂ) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  letI : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  exact gaussSum χ (eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates a ha) / (‖eisEmbedding a‖ : ℂ)

noncomputable def normalizedTraceGaussProduct
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) : ℂ := by
  letI : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  letI : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    χa (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    χb (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
      a b ha hb x) / (‖eisEmbedding (a * b)‖ : ℂ)

theorem normalizedTraceGaussProduct_crt
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    normalizedTraceGaussProduct a b ha hb χa χb =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      normalizedTraceGauss a ha χa * normalizedTraceGauss b hb χb := by
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  have hsum := gauss_sum_breveE_actual_O a b ha hb hcop χa χb
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) =
      (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul]
    norm_cast
  change (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    χa (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    χb (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates a b ha hb x) /
      (‖eisEmbedding (a * b)‖ : ℂ) = _
  rw [hsum, hnorm]
  unfold normalizedTraceGauss
  ring

end ConcreteBreveE

namespace FixedRayActiveSet

open scoped BigOperators

private theorem sum_zero_and_units {F : Type*} [Field F] [Fintype F]
    (f : F → ℂ) :
    (∑ x : F, f x) = f 0 + ∑ u : Fˣ, f (u : F) := by
  classical
  calc
    (∑ x : F, f x) = f 0 +
        ∑ x ∈ (Finset.univ : Finset F).erase 0, f x := by
          simpa only [add_comm] using
            (Finset.sum_erase_add (Finset.univ : Finset F) f
              (Finset.mem_univ (0 : F))).symm
    _ = f 0 + ∑ x : {x : F // x ≠ 0}, f x := by
      congr 1
      apply Finset.sum_subtype
      intro x
      simp
    _ = f 0 + ∑ u : Fˣ, f (u : F) := by
      congr 1
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun u : Fˣ => f (u : F))
        (fun x : {x : F // x ≠ 0} => f x) ?_).symm
      intro u
      rfl

theorem product_sum_by_active_set
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (f : ∀ i, F i → ℂ) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ (Finset.univ : Finset ι).powerset,
        (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by
  classical
  calc
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
        ∏ i, ∑ h : F i, f i h := by
          simpa using (Fintype.prod_sum (fun i (h : F i) => f i h)).symm
    _ = ∏ i, ((∑ u : (F i)ˣ, f i (u : F i)) + f i 0) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [sum_zero_and_units]
      ring
    _ = _ := Finset.prod_add
      (fun i => ∑ u : (F i)ˣ, f i (u : F i))
      (fun i => f i 0) Finset.univ

theorem branch_zero_of_local_mask
    {ι : Type*} [DecidableEq ι] (I A : Finset ι)
    (scalar dual inactive : ι → ℂ)
    (i : ι) (hi : i ∈ A) (hzero : dual i = 0) :
    (∏ k ∈ A, scalar k * dual k) *
      (∏ k ∈ I \ A, inactive k) = 0 := by
  have hprod : (∏ k ∈ A, scalar k * dual k) = 0 :=
    Finset.prod_eq_zero hi (by rw [hzero, mul_zero])
  rw [hprod, zero_mul]

theorem admissible_branch_count
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) :
    ((Finset.univ : Finset ι).powerset.filter
      (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)).card
      ≤ 2 ^ Fintype.card ι := by
  calc
    _ ≤ (Finset.univ : Finset ι).powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card ι := by simp

private theorem branch_zero_outside_admissible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) (scalar dual inactive : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → inactive i = 0)
    (A : Finset ι)
    (hnot : ¬ (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A) :
    (∏ i ∈ A, scalar i * dual i) *
      (∏ i ∈ (Finset.univ : Finset ι) \ A, inactive i) = 0 := by
  obtain ⟨i, hiM, hiA⟩ := Finset.not_subset.mp hnot
  have hj : j i ≠ 0 := (Finset.mem_filter.mp hiM).2
  have hi : i ∈ (Finset.univ : Finset ι) \ A := by simp [hiA]
  have hprod : (∏ k ∈ (Finset.univ : Finset ι) \ A, inactive k) = 0 :=
    Finset.prod_eq_zero hi (hzero i hj)
  rw [hprod, mul_zero]

theorem assemble_local_A5
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (j : ι → ℕ) (f : ∀ i, F i → ℂ)
    (scalar dual : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → f i 0 = 0)
    (hactive : ∀ i, (∑ u : (F i)ˣ, f i (u : F i)) =
      scalar i * dual i) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, scalar i * dual i) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by
  classical
  rw [product_sum_by_active_set]
  have hreplace : ∀ A : Finset ι,
      (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) =
        ∏ i ∈ A, scalar i * dual i := by
    intro A
    apply Finset.prod_congr rfl
    intro i _
    exact hactive i
  conv_lhs =>
    arg 2
    ext A
    rw [hreplace A]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hAdmissible : (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A
  · simp [hAdmissible]
  · simp [hAdmissible,
      branch_zero_outside_admissible j scalar dual (fun i => f i 0)
        (fun i hj => hzero i hj)
        A hAdmissible]

end FixedRayActiveSet

namespace CubeInversion

theorem cube_index_filter_complex (m : ℕ) :
    (∑ h ∈ m.divisors, (ArithmeticFunction.moebius h : ℂ)) =
      if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact_mod_cast h

theorem cube_coefficient_filter
    (m : ℕ) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      if m = 1 then c m * W m else 0 := by
  have heq (h : ℕ) (hh : h ∈ m.divisors) :
      c h * c (m / h) = c m := by
    rw [← hc]
    congr 1
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hh)
  calc
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      (∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ)) * (c m * W m) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h hh
        calc
          (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m =
              (ArithmeticFunction.moebius h : ℂ) * (c h * c (m / h)) * W m := by ring
          _ = (ArithmeticFunction.moebius h : ℂ) * (c m * W m) := by
              rw [heq h hh]
              ring
    _ = if m = 1 then c m * W m else 0 := by
      rw [cube_index_filter_complex]
      split_ifs <;> simp

theorem finite_cube_inversion
    (S : Finset ℕ) (hS : 1 ∈ S) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ m ∈ S, ∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
        c 1 * W 1 := by
  simp_rw [cube_coefficient_filter (c := c) (W := W) (hc := hc)]
  simp [hS]

theorem finite_cube_inversion_with_columns {N : Type*} [DecidableEq N]
    (columns : Finset N) (S : Finset ℕ) (hS : 1 ∈ S)
    (a : N → ℂ) (c : ℕ → ℂ) (W : N → ℕ → ℂ)
    (hc : ∀ x y, c (x * y) = c x * c y) :
    (∑ n ∈ columns, a n *
      (∑ m ∈ S, ∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W n m)) =
      ∑ n ∈ columns, a n * (c 1 * W n 1) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [finite_cube_inversion S hS c (W n) hc]

end CubeInversion

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveGammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)⁻¹
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

private theorem canonicalSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (canonicalSextic P hgood) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  change orderOf (Φ (sexticChar P hgood)) = 6
  rw [orderOf_injective Φ hΦ, sexticChar_order P hgood hchar]

theorem breveGamma1_gammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGammaMinus1 P hgood p hP hp =
      canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)) := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have horder : orderOf χ = 6 :=
    canonicalSextic_order_six (Ideal.span {p}) hgood hchar
  have hχ5 : χ ^ 5 = χ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ * χ ^ 5 = χ ^ 6 := by group
      _ = 1 := hχ6
  have hprod := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ
  rw [horder, show 6 - 1 = 5 by decide, hχ5] at hprod
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  change (gaussSum χ ψ / s) * (gaussSum χ⁻¹ ψ / s) = χ (-1)
  field_simp
  rw [hs]
  simpa only [mul_comm] using hprod

end ActualEisensteinCubic

namespace PowerExtraction

theorem from_mean_square_and_prime_rows
    (D ε J A : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A)
    (hJ : D ^ ((11 / 60 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((21 / 10 : ℝ) + ε) +
      2 * J * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((21 / 10 : ℝ) + ε) ≤
        J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hsq : A ^ 2 ≤ 4 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * D ^ (49 / 30 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              gcongr
        _ = 4 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) := (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, hpow2]
  nlinarith

end PowerExtraction

end

end OAI

end


