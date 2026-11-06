-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
-- name    : OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:35:44.392443+00:00
-- url     : https://prove2.me/theorems/4721fdfb-e084-4b11-bbda-6786b336a9ed
-- title:
--   Eisenstein Embedding
-- statement:
--   Definitions and structural lemmas for Eisenstein Embedding, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftTrace_breveE_period_lam
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
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
instance : IsCyclotomicExtension {3} ℚ K :=
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
end ConcreteBreveE
namespace ActualEisensteinCubic
open AddChar MulChar
open AddChar MulChar
noncomputable def canonicalSextic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) ℂ :=
  (sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding
end ActualEisensteinCubic
namespace PrimitiveTrace
open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT
end PrimitiveTrace
end
end OAI


