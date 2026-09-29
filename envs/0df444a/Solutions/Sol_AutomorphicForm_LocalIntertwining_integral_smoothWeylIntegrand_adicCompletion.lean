-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ecfe7417-5c78-5bd2-a4b6-2a53f7c12cb2

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion

set_option autoImplicit false

section FinGKFold_ValuationOrd

namespace M4aP2DGK
namespace FinGK
namespace ValuationOrd

open Ideal IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

private theorem exists_span_eq_pow {a : A} (ha : a ≠ 0) :
    ∃ n, span {a} = maximalIdeal A ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [span_singleton_eq_span_singleton.mpr hn, ← span_singleton_pow, ← hϖ.maximalIdeal_eq]

private theorem pow_maximalIdeal_ne_of_lt {n k : ℕ} (h : n < k) :
    (maximalIdeal A) ^ n ≠ maximalIdeal A ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro heq
  have hmem : ϖ ^ n ∈ maximalIdeal A ^ k := by
    rw [← heq, hϖ.maximalIdeal_eq, span_singleton_pow]
    exact mem_span_singleton_self _
  rw [hϖ.maximalIdeal_eq, span_singleton_pow, mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : (1 : A) = ϖ ^ (k - n) * c := by
    refine mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) ?_
    rw [mul_one, ← mul_assoc, ← pow_add]
    rw [show n + (k - n) = k from by omega]
    exact hc
  have hkn : k - n - 1 + 1 = k - n := by omega
  exact hϖ.not_isUnit (isUnit_of_dvd_one ⟨ϖ ^ (k - n - 1) * c, by
    rw [h1, ← mul_assoc, ← pow_succ', hkn]⟩)

private theorem pow_maximalIdeal_injective {n k : ℕ}
    (h : (maximalIdeal A) ^ n = maximalIdeal A ^ k) : n = k := by
  rcases Nat.lt_trichotomy n k with hlt | heq | hgt
  · exact absurd h (pow_maximalIdeal_ne_of_lt A hlt)
  · exact heq
  · exact absurd h.symm (pow_maximalIdeal_ne_of_lt A hgt)

open Classical in
private noncomputable def ordA (a : A) : ℕ :=
  if h : a = 0 then 0 else (exists_span_eq_pow A h).choose

private theorem ordA_span {a : A} (ha : a ≠ 0) :
    span {a} = maximalIdeal A ^ ordA A a := by
  classical
  rw [ordA, dif_neg ha]
  exact (exists_span_eq_pow A ha).choose_spec

private theorem ordA_unique {a : A} (ha : a ≠ 0) {n : ℕ}
    (h : span {a} = maximalIdeal A ^ n) : ordA A a = n :=
  pow_maximalIdeal_injective A ((ordA_span A ha).symm.trans h)

private theorem ordA_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordA A (a * b) = ordA A a + ordA A b := by
  refine ordA_unique A (mul_ne_zero ha hb) ?_
  rw [← span_singleton_mul_span_singleton, ordA_span A ha, ordA_span A hb, pow_add]

open Classical in
private noncomputable def ordZ (x : Lˣ) : ℤ :=
  if h : (x : L) ∈ A then (ordA A ⟨(x : L), h⟩ : ℤ)
  else -(ordA A ⟨((x⁻¹ : Lˣ) : L), by
    rw [Units.val_inv_eq_inv_val]
    exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ : ℤ)

omit [IsDiscreteValuationRing ↥A] in
private theorem coe_mk_ne_zero (x : Lˣ) {y : L} (hy : y ∈ A) (hxy : y = (x : L)) :
    (⟨y, hy⟩ : A) ≠ 0 := by
  intro h0
  have : y = 0 := congrArg Subtype.val h0
  exact x.ne_zero (hxy ▸ this)

private theorem ordZ_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) : ordZ A x = (ordA A a : ℤ) - ordA A b := by
  classical
  by_cases h : (x : L) ∈ A
  · rw [ordZ, dif_pos h]
    have hab : (⟨(x : L), h⟩ : A) * b = a := Subtype.ext hx
    have hmul := ordA_mul A (coe_mk_ne_zero A x h rfl) hb
    rw [hab] at hmul
    omega
  · rw [ordZ, dif_neg h]
    set c : A := ⟨((x⁻¹ : Lˣ) : L), by
      rw [Units.val_inv_eq_inv_val]
      exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ with hc
    have hcx : (c : A) ≠ 0 := coe_mk_ne_zero A x⁻¹ _ rfl
    have hab : a * c = b := by
      refine Subtype.ext ?_
      push_cast
      have hcL : (c : L) = ((x : L))⁻¹ := by rw [hc]; exact Units.val_inv_eq_inv_val x
      rw [hcL, ← hx, mul_comm ((x : L)) ((b : L)), mul_assoc,
        mul_inv_cancel₀ x.ne_zero, mul_one]
    have hmul := ordA_mul A ha hcx
    rw [hab] at hmul
    omega

omit [IsDiscreteValuationRing ↥A] in
private theorem exists_rep (x : Lˣ) :
    ∃ a b : A, a ≠ 0 ∧ b ≠ 0 ∧ (x : L) * (b : L) = (a : L) := by
  rcases A.mem_or_inv_mem (x : L) with h | h
  · exact ⟨⟨(x : L), h⟩, 1, coe_mk_ne_zero A x h rfl, one_ne_zero, by
      push_cast; exact mul_one _⟩
  · refine ⟨1, ⟨((x⁻¹ : Lˣ) : L), by rwa [Units.val_inv_eq_inv_val]⟩,
      one_ne_zero, coe_mk_ne_zero A x⁻¹ _ rfl, ?_⟩
    show (x : L) * ((x⁻¹ : Lˣ) : L) = (1 : L)
    exact x.mul_inv

private noncomputable def ord : Additive Lˣ →+ ℤ where
  toFun x := ordZ A x.toMul
  map_zero' := by
    show ordZ A (1 : Lˣ) = 0
    have h1 := ordZ_spec A (x := 1) (a := 1) (b := 1) one_ne_zero one_ne_zero
      (by rw [Units.val_one, one_mul])
    rw [h1]
    ring
  map_add' x y := by
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x.toMul
    obtain ⟨c, d, hc, hd, hy⟩ := exists_rep A y.toMul
    have hxy : (((x + y).toMul : Lˣ) : L) * ((b * d : A) : L) = ((a * c : A) : L) := by
      push_cast
      calc (x.toMul : L) * (y.toMul : L) * ((b : L) * (d : L))
          = ((x.toMul : L) * (b : L)) * ((y.toMul : L) * (d : L)) := by ring
        _ = (a : L) * (c : L) := by rw [hx, hy]
    show ordZ A (x + y).toMul = ordZ A x.toMul + ordZ A y.toMul
    rw [ordZ_spec A (mul_ne_zero ha hc) (mul_ne_zero hb hd) hxy,
      ordZ_spec A ha hb hx, ordZ_spec A hc hd hy, ordA_mul A ha hc, ordA_mul A hb hd]
    push_cast
    ring

private theorem ord_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) {na nb : ℕ}
    (hna : span {a} = maximalIdeal A ^ na) (hnb : span {b} = maximalIdeal A ^ nb) :
    ord A (.ofMul x) = (na : ℤ) - nb := by
  have := ordZ_spec A ha hb hx
  rw [ordA_unique A ha hna, ordA_unique A hb hnb] at this
  exact this

private theorem ord_ofMul_of_mem {x : Lˣ} (hx : (x : L) ∈ A) {n : ℕ}
    (hspan : span {(⟨(x : L), hx⟩ : A)} = maximalIdeal A ^ n) :
    ord A (.ofMul x) = n := by
  have h := ord_spec A (coe_mk_ne_zero A x hx rfl) one_ne_zero
    (b := 1) (by push_cast; exact mul_one _) hspan
    (by rw [span_singleton_eq_top.mpr isUnit_one, pow_zero, one_eq_top])
  simpa using h

private theorem ord_ofMul_mk0_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : A) : L) ≠ 0) :
    ord A (.ofMul (Units.mk0 ((ϖ : A) : L) h0)) = 1 := by
  refine ord_ofMul_of_mem A (x := Units.mk0 ((ϖ : A) : L) h0) (ϖ : A).2 ?_
  have hmk : (⟨((Units.mk0 ((ϖ : A) : L) h0 : Lˣ) : L), (ϖ : A).2⟩ : A) = ϖ :=
    Subtype.ext rfl
  rw [hmk, pow_one, ← hϖ.maximalIdeal_eq]

private theorem ord_eq_zero_iff (x : Lˣ) :
    ord A (.ofMul x) = 0 ↔ x ∈ (Units.map (A.subtype.toMonoidHom)).range := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x
    have hspec : ordZ A x = (ordA A a : ℤ) - ordA A b := ordZ_spec A ha hb hx
    have h0 : ordZ A x = 0 := h
    have hord : ordA A a = ordA A b := by omega
    have hassoc : Associated a b := span_singleton_eq_span_singleton.mp
      (by rw [ordA_span A ha, ordA_span A hb, hord])
    obtain ⟨u, hu⟩ := hassoc
    have haL : (a : L) ≠ 0 := fun hz => ha (Subtype.ext hz)
    have hab : (a : L) * (((u : Aˣ) : A) : L) = (b : L) := by
      exact_mod_cast congrArg (fun s : A => (s : L)) hu
    have h1 : (x : L) * (((u : Aˣ) : A) : L) = 1 := by
      have h2 : (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) = (a : L) := by
        rw [hab]; exact hx
      have h3 : ((x : L) * (((u : Aˣ) : A) : L)) * (a : L) = 1 * (a : L) := by
        rw [one_mul]
        calc ((x : L) * (((u : Aˣ) : A) : L)) * (a : L)
            = (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) := by ring
          _ = (a : L) := h2
      exact mul_right_cancel₀ haL h3
    have huL : (((u : Aˣ) : A) : L) * (((u⁻¹ : Aˣ) : A) : L) = 1 := by
      exact_mod_cast congrArg (fun s : A => (s : L)) u.mul_inv
    have hxinv : (x : L) = ((((u : Aˣ) : A) : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have huinv : (((u⁻¹ : Aˣ) : A) : L) = ((((u : Aˣ) : A) : L))⁻¹ :=
      eq_inv_of_mul_eq_one_right huL
    refine ⟨u⁻¹, Units.ext ?_⟩
    show (((u⁻¹ : Aˣ) : A) : L) = (x : L)
    rw [huinv, hxinv]
  · rintro ⟨u, rfl⟩
    have hmem : ((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L) ∈ A := by
      show ((A.subtype) ((u : Aˣ) : A) : L) ∈ A
      exact ((u : Aˣ) : A).2
    have hspan : span {(⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A)}
        = maximalIdeal A ^ 0 := by
      rw [show (⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A) = ((u : Aˣ) : A)
        from Subtype.ext rfl]
      rw [span_singleton_eq_top.mpr u.isUnit, pow_zero, one_eq_top]
    have := ord_ofMul_of_mem A hmem hspan
    simpa using this

end ValuationOrd
end M4aP2DGK.FinGK

end FinGKFold_ValuationOrd

section FinGKFold_LocalHaarModulus

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open scoped NNReal ENNReal Pointwise

namespace M4aP2DGK
namespace FinGK
namespace LocalHaarModulus

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

private theorem card_residueField_pos :
    0 < Nat.card (ResidueField (v.adicCompletionIntegers F)) :=
  Nat.card_pos

section CosetStep

variable {F v}

private theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (Y : v.adicCompletionIntegers F) :
    ∃ z : v.adicCompletionIntegers F,
      Y = Quotient.out (residue (v.adicCompletionIntegers F) Y) + ϖ * z := by
  have hout : residue (v.adicCompletionIntegers F)
      (Quotient.out (residue (v.adicCompletionIntegers F) Y))
      = residue (v.adicCompletionIntegers F) Y := Quotient.out_eq _
  have hzero : residue (v.adicCompletionIntegers F)
      (Y - Quotient.out (residue (v.adicCompletionIntegers F) Y)) = 0 := by
    rw [map_sub, hout, sub_self]
  set w : v.adicCompletionIntegers F
      := Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) with hw
  have hmem : w ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hsub : Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) = ϖ * z := by
    rw [← hw]; exact hz
  exact sub_eq_iff_eq_add'.mp hsub

private theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

private abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

private theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers F)
    refine mem_iUnion.mpr ⟨residue (v.adicCompletionIntegers F) ⟨y, hy⟩, ?_⟩
    refine ⟨(z : v.adicCompletion F), z.2, ?_⟩
    have hco := congrArg
      (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := hk
    obtain ⟨X, hXy⟩ : ∃ X : v.adicCompletionIntegers F, (X : v.adicCompletion F) = y :=
      ⟨Quotient.out k + ϖ * ⟨z, hz⟩, by push_cast; exact hzy⟩
    rw [← hXy]
    exact X.2

private theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint fun k : ResidueField (v.adicCompletionIntegers F) =>
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hKeq : ((Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F) :
      v.adicCompletion F)
      = ((Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :
          v.adicCompletion F) := by
    push_cast
    rw [show ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z = y from hzy,
        show ((Quotient.out k' : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z' = y from hzy']
  have hAeq : (Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F)
      = (Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :=
    Subtype.coe_injective hKeq
  have := congrArg (residue (v.adicCompletionIntegers F)) hAeq
  rwa [residue_out_add_mul hϖ, residue_out_add_mul hϖ] at this

private theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
    (k : ResidueField (v.adicCompletionIntegers F)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
          (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

end CosetStep

section Measure

variable {F v}

private theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  have hTopen : IsOpen (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (NumberField.isOpenAdicCompletionIntegers F v).smul₀ hϖ0
  have hTmeas := hTopen.measurableSet
  have hbridge : ∀ k : ResidueField (v.adicCompletionIntegers F),
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun k => cosetMap_image_eq k
  calc μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = μ (⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        rw [← integers_eq_iUnion_image hϖ]
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine measure_iUnion ?_ fun k => ?_
        · intro k k' hkk'
          exact pairwise_disjoint_image hϖ hkk'
        · rw [hbridge k]
          exact hTmeas.const_vadd _
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := by
        exact tsum_congr fun k => by rw [hbridge k]
    _ = ∑' _ : ResidueField (v.adicCompletionIntegers F),
          μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine tsum_congr fun k => ?_
        exact measure_vadd _ _ _
    _ = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]

end Measure

section MainTheorem

variable {F v}

private theorem distribHaarChar_eq_one_of_mem_range (x : (v.adicCompletion F)ˣ)
    (hx : x ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range) :
    distribHaarChar (v.adicCompletion F) x = 1 := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  obtain ⟨u, rfl⟩ := hx
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨μ⟩ : Nonempty {μ : Measure (v.adicCompletion F) // μ.IsAddHaarMeasure ∧ μ.Regular} :=
    ⟨⟨(MeasureTheory.Measure.addHaarMeasure
        ⟨⟨S, hK⟩, by
          rw [interior_eq_iff_isOpen.mpr hO]
          exact ⟨0, Subring.zero_mem _⟩⟩),
      inferInstance, inferInstance⟩⟩
  obtain ⟨μ, hHaar, hReg⟩ := μ
  haveI := hHaar; haveI := hReg
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S)
    (hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩) (hK.measure_lt_top.ne) ?_
  have hset : ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)) u : _) • S = S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_mem ((u : v.adicCompletionIntegers F).2) hz
    · intro hy
      set w : v.adicCompletionIntegers F := ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
        v.adicCompletionIntegers F) with hw
      refine ⟨(w : v.adicCompletion F) * y, mul_mem w.2 hy, ?_⟩
      have hcancel : ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * (w : v.adicCompletion F) = 1 := by
        have : ((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F)
            = (1 : v.adicCompletionIntegers F) := by
          rw [hw]
          exact_mod_cast u.mul_inv
        calc ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * (w : v.adicCompletion F)
            = (((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F) :
                v.adicCompletion F) := by rw [Subring.coe_mul]
          _ = 1 := by rw [this]; rfl
      show ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((w : v.adicCompletion F) * y) = y
      rw [← mul_assoc, hcancel, one_mul]
  rw [hset, ENNReal.coe_one, one_mul]

private theorem distribHaarChar_mk0_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0) :
    distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  set μ : Measure (v.adicCompletion F) := MeasureTheory.Measure.addHaarMeasure
    ⟨⟨S, hK⟩, by
      rw [interior_eq_iff_isOpen.mpr hO]
      exact ⟨0, Subring.zero_mem _⟩⟩ with hμ
  have hq0 : (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos
  have hS0 : μ S ≠ 0 := hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩
  have hSfin : μ S ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S) hS0 hSfin ?_
  have hcount := measure_integers_eq_card_mul μ hϖ
  show μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) • S)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ * μ S
  rw [ENNReal.coe_inv (by exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos), ENNReal.coe_natCast]
  rw [hcount]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]

private theorem distribHaarChar_adicCompletion (x : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) x
      = ((Ideal.absNorm v.asIdeal : ℝ≥0))
          ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  set w : (v.adicCompletion F)ˣ := Units.mk0 _ h0 with hw
  set k : ℤ := ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) with hk
  set y : (v.adicCompletion F)ˣ := x * w ^ (-k) with hy
  have hordw : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 1 :=
    ValuationOrd.ord_ofMul_mk0_of_irreducible (v.adicCompletionIntegers F) hϖ h0
  have hordy : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul y) = 0 := by
    have hmul : Additive.ofMul y = Additive.ofMul x + (-k) • Additive.ofMul w := rfl
    rw [hmul, map_add, map_zsmul, hordw, smul_eq_mul, mul_one, ← hk, add_neg_cancel]
  have hyunit : distribHaarChar (v.adicCompletion F) y = 1 :=
    distribHaarChar_eq_one_of_mem_range y
      ((ValuationOrd.ord_eq_zero_iff (v.adicCompletionIntegers F) y).mp hordy)
  have hxy : x = y * w ^ k := by
    rw [hy, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hqw : distribHaarChar (v.adicCompletion F) w
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ :=
    distribHaarChar_mk0_irreducible hϖ h0
  rw [hxy, map_mul, map_zpow, hyunit, one_mul, hqw, inv_zpow, ← zpow_neg,
    card_residueField_eq_absNorm]

private theorem measure_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] [μ.Regular] (x : (v.adicCompletion F)ˣ) :
    μ ((x : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (((Ideal.absNorm v.asIdeal : ℝ≥0))
          ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) : ℝ≥0)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [← distribHaarChar_adicCompletion, distribHaarChar_mul]
  rfl

end MainTheorem

end

end LocalHaarModulus
end M4aP2DGK.FinGK

end FinGKFold_LocalHaarModulus

section FinGKFold_LocalZetaUnramified

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aP2DGK
namespace FinGK
namespace LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private abbrev normQ (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)

private theorem modulus_of_ne_zero_adicCompletion {x : v.adicCompletion F} (hx : x ≠ 0) :
    modulus x = normQ v ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F)
      (Additive.ofMul (Units.mk0 x hx)))) := by
  rw [modulus_of_ne_zero hx]
  exact LocalHaarModulus.distribHaarChar_adicCompletion (Units.mk0 x hx)

section Shells

variable {ϖ : v.adicCompletionIntegers F}

private theorem coe_ne_zero_of_irreducible (hϖ : Irreducible ϖ) :
    ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)

private def piUnit (hϖ : Irreducible ϖ) : (v.adicCompletion F)ˣ := Units.mk0 _ (coe_ne_zero_of_irreducible hϖ)

@[scoped simp] private theorem piUnit_val (hϖ : Irreducible ϖ) :
    ((piUnit hϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl

private theorem ord_piUnit (hϖ : Irreducible ϖ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ)) = 1 :=
  ValuationOrd.ord_ofMul_mk0_of_irreducible _ hϖ _

private theorem ord_piUnit_pow (hϖ : Irreducible ϖ) (k : ℕ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ((piUnit hϖ) ^ k)) = k := by
  have h : Additive.ofMul ((piUnit hϖ) ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_nsmul, ord_piUnit]
  simp

private def shellSet (hϖ : Irreducible ϖ) (k : ℕ) : Set (v.adicCompletion F) :=
  (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    \ (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

private theorem isCompact_integers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  NumberField.isCompactAdicCompletionIntegers F v

private theorem isCompact_smul_integers (c : v.adicCompletion F) :
    IsCompact (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have h := (isCompact_integers (F := F) (v := v)).image (continuous_const_smul c)
  rwa [Set.image_smul] at h

private theorem measurableSet_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (c : v.adicCompletion F) :
    MeasurableSet (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  (isCompact_smul_integers c).isClosed.measurableSet

private theorem measurableSet_shellSet [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (hϖ : Irreducible ϖ) (k : ℕ) :
    MeasurableSet (shellSet hϖ k) :=
  (measurableSet_smul_integers _).diff (measurableSet_smul_integers _)

private theorem mem_smul_integers_iff {c x : v.adicCompletion F} :
    x ∈ c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ↔ ∃ y : v.adicCompletionIntegers F, c * (y : v.adicCompletion F) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, (smul_eq_mul c y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y : v.adicCompletion F), y.2, by show c • (y : v.adicCompletion F) = x; rw [smul_eq_mul]; exact hy⟩

private theorem shellSet_subset_integers (hϖ : Irreducible ϖ) (k : ℕ) :
    shellSet hϖ k ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hx.1
  rw [← hy]
  push_cast [piUnit_val]
  exact mul_mem (pow_mem ϖ.2 k) y.2

private theorem zero_notMem_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : (0 : v.adicCompletion F) ∉ shellSet hϖ k := by
  intro h
  exact h.2 (mem_smul_integers_iff.mpr ⟨0, by push_cast; ring⟩)

private theorem mem_shellSet_iff_ord_eq (hϖ : Irreducible ϖ) (k : ℕ) {x : v.adicCompletion F} (hx : x ≠ 0) :
    x ∈ shellSet hϖ k
      ↔ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx))
          = k := by
  constructor
  · intro hmem
    obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hmem.1
    have hy0 : (y : v.adicCompletion F) ≠ 0 := by
      intro h0
      exact hx (by rw [← hy, h0, mul_zero])
    have hyunit : IsUnit y := by
      by_contra hnu
      have hymem : y ∈ maximalIdeal (v.adicCompletionIntegers F) := hnu
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hymem
      obtain ⟨z, hz⟩ := hymem
      refine hmem.2 (mem_smul_integers_iff.mpr ⟨z, ?_⟩)
      rw [← hy, hz]
      push_cast [pow_succ, piUnit_val]
      ring
    obtain ⟨u, hu⟩ := hyunit
    have hxfac : Units.mk0 x hx
        = piUnit hϖ ^ k
          * Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u := by
      ext
      rw [Units.val_mk0, ← hy]
      push_cast [piUnit_val, Units.coe_map]
      rw [← hu]
      rfl
    have hordu : ValuationOrd.ord (v.adicCompletionIntegers F)
        (Additive.ofMul (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u))
          = 0 :=
      (ValuationOrd.ord_eq_zero_iff _ _).mpr ⟨u, rfl⟩
    have hsplit : Additive.ofMul (Units.mk0 x hx)
        = Additive.ofMul (piUnit hϖ ^ k)
          + Additive.ofMul (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u) := by
      rw [hxfac]; rfl
    rw [hsplit, map_add, hordu, add_zero, ord_piUnit_pow]
  · intro hord
    set w : (v.adicCompletion F)ˣ := Units.mk0 x hx * (piUnit hϖ ^ k)⁻¹ with hwdef
    have hword : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
      have hsub : Additive.ofMul w = Additive.ofMul (Units.mk0 x hx)
          - Additive.ofMul (piUnit hϖ ^ k) := rfl
      rw [hsub, map_sub, hord, ord_piUnit_pow, sub_self]
    obtain ⟨u, hu⟩ := (ValuationOrd.ord_eq_zero_iff _ _).mp hword
    have hxw : x = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      have hfac : Units.mk0 x hx = piUnit hϖ ^ k * w := by
        rw [hwdef, mul_comm (Units.mk0 x hx) ((piUnit hϖ ^ k)⁻¹), mul_inv_cancel_left]
      calc x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
        _ = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
              rw [hfac, Units.val_mul]
    constructor
    · have hwmem : ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          ∈ v.adicCompletionIntegers F := by
        rw [← hu]
        exact ((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
      exact mem_smul_integers_iff.mpr
        ⟨⟨((w : (v.adicCompletion F)ˣ) : v.adicCompletion F), hwmem⟩, hxw.symm⟩
    · intro hnext
      obtain ⟨z, hz⟩ := mem_smul_integers_iff.mp hnext
      have hcan : ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            * (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * (z : v.adicCompletion F)) := by
        rw [← hxw, ← hz]
        push_cast [pow_succ, piUnit_val]
        ring
      have hwz := mul_left_cancel₀ (Units.ne_zero (piUnit hϖ ^ k)) hcan
      have hwmem : ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
        rw [hwz]; exact mul_mem ϖ.2 z.2
      obtain ⟨uw, huw⟩ := (ValuationOrd.ord_eq_zero_iff _ _).mp hword
      have huwO : ((uw : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          = ϖ * z := by
        apply Subtype.coe_injective
        push_cast
        calc ((uw : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F)
            = ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) uw
                : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
          _ = ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by rw [huw]
          _ = _ := by rw [hwz]
      have hunit : IsUnit ((ϖ : v.adicCompletionIntegers F) * z) := huwO ▸ uw.isUnit
      exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left hunit)

end Shells

private theorem one_le_normQ : (1 : ℝ≥0) ≤ normQ v := by
  have hpos := LocalHaarModulus.card_residueField_pos (F := F) (v := v)
  have hcard := LocalHaarModulus.card_residueField_eq_absNorm (F := F) (v := v)
  have h1 : 1 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h1

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable {ϖ : v.adicCompletionIntegers F}
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace (v.adicCompletion F)] [μ.Regular] in
private theorem measure_integers_lt_top : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ :=
  (isCompact_integers (F := F) (v := v)).measure_lt_top

end Measures

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

private theorem ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ) :
    (((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg ha n) ha, ih,
        pow_succ]

end Integrand

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable {ϖ : v.adicCompletionIntegers F}
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Zeta

end LocalZetaUnramified
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_LocalZetaUnramified
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section FinGKFold_MulHaarFromAdditive

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aP2DGK
namespace FinGK
namespace MulHaarFromAdditive

open LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have hr : Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F)
      = {(0 : v.adicCompletion F)}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [hr]
  exact isClosed_singleton.isOpen_compl

private theorem image_val_subset_compl_zero (A : Set (v.adicCompletion F)ˣ) :
    (Units.val '' A) ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

private theorem smul_set_eq_preimage {c : v.adicCompletion F} (hc : c ≠ 0)
    (S : Set (v.adicCompletion F)) :
    c • S = (fun y => c⁻¹ * y) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

private theorem isOpen_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : IsOpen S) :
    IsOpen (c • S) := by
  have h : c • S = (Homeomorph.mulLeft₀ c hc) '' S := by
    ext x
    simp [Homeomorph.coe_mulLeft₀, Set.mem_smul_set, smul_eq_mul, Set.mem_image]
  rw [h]
  exact (Homeomorph.mulLeft₀ c hc).isOpenMap _ hS

private theorem image_val_smul (g : (v.adicCompletion F)ˣ) (A : Set (v.adicCompletion F)ˣ) :
    Units.val '' (g • A) = (g : v.adicCompletion F) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : v.adicCompletion F), ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g * a, ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩

variable {ϖ : v.adicCompletionIntegers F}

private theorem isOpen_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : IsOpen (shellSet hϖ k) := by
  unfold shellSet
  refine IsOpen.sdiff (isOpen_smul_set (Units.ne_zero _) ?_) ?_
  · exact Valued.isOpen_valuationSubring _
  · rw [smul_set_eq_preimage (Units.ne_zero _)]
    exact (Valued.isClosed_valuationSubring _).preimage (continuous_const_mul _)

private theorem one_mem_shellSet_zero (hϖ : Irreducible ϖ) :
    (1 : v.adicCompletion F) ∈ shellSet hϖ 0 := by
  have h10 : (1 : v.adicCompletion F) ≠ 0 := one_ne_zero
  rw [mem_shellSet_iff_ord_eq hϖ 0 h10]
  have h1 : Units.mk0 (1 : v.adicCompletion F) h10 = 1 := Units.ext (by simp)
  rw [h1]
  simp

private theorem ord_ofMul_mul (u w : (v.adicCompletion F)ˣ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (u * w))
      = ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u)
        + ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) := by
  have h : Additive.ofMul (u * w) = Additive.ofMul u + Additive.ofMul w := rfl
  rw [h, map_add]

private theorem ord_ofMul_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ ^ k)) = k := by
  have h : Additive.ofMul (piUnit hϖ ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_zsmul, ord_piUnit hϖ, smul_eq_mul, mul_one]

private def genShell (hϖ : Irreducible ϖ) (k : ℤ) : Set (v.adicCompletion F) :=
  ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0

private theorem mem_genShell_iff (hϖ : Irreducible ϖ) {k : ℤ} {x : v.adicCompletion F} (hx : x ≠ 0) :
    x ∈ genShell hϖ k
      ↔ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx)) = k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    have hu : Units.mk0 _ hx = piUnit hϖ ^ k * Units.mk0 y hy0 :=
      Units.ext (by simp [smul_eq_mul])
    rw [hu, ord_ofMul_mul, ord_ofMul_zpow_piUnit hϖ,
      (mem_shellSet_iff_ord_eq hϖ 0 hy0).mp hy]
    simp
  · intro hord
    have hne : (((piUnit hϖ ^ k)⁻¹ * Units.mk0 x hx : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) ≠ 0 := Units.ne_zero _
    refine ⟨_, (mem_shellSet_iff_ord_eq hϖ 0 hne).mpr ?_, ?_⟩
    · have hmk : Units.mk0 _ hne = (piUnit hϖ ^ k)⁻¹ * Units.mk0 x hx :=
        Units.ext (by simp)
      rw [hmk, ord_ofMul_mul,
        show ((piUnit hϖ ^ k)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hϖ ^ (-k) from
          (zpow_neg _ _).symm,
        ord_ofMul_zpow_piUnit hϖ, hord]
      simp
    · show (↑(piUnit hϖ ^ k) : v.adicCompletion F) • _ = x
      rw [smul_eq_mul, ← Units.val_mul, mul_inv_cancel_left, Units.val_mk0]

private theorem genShell_disjoint (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint (genShell hϖ)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro x hxk hxl
  have hx : x ≠ 0 := by
    rcases hxk with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [smul_eq_mul]
    exact mul_ne_zero (Units.ne_zero _) hy0
  exact hkl (((mem_genShell_iff hϖ hx).mp hxk).symm.trans ((mem_genShell_iff hϖ hx).mp hxl))

private theorem iUnion_genShell (hϖ : Irreducible ϖ) :
    (⋃ k : ℤ, genShell hϖ k) = {(0 : v.adicCompletion F)}ᶜ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [smul_eq_mul]
    exact mul_ne_zero (Units.ne_zero _) hy0
  · intro hx
    exact ⟨_, (mem_genShell_iff hϖ hx).mpr rfl⟩

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

private theorem measurableSet_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : MeasurableSet S) :
    MeasurableSet (c • S) := by
  rw [smul_set_eq_preimage hc]
  exact hS.preimage (measurable_const_mul _)

private theorem measurableSet_genShell (hϖ : Irreducible ϖ) (k : ℤ) :
    MeasurableSet (genShell hϖ k) :=
  measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0)

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace (v.adicCompletion F)] [μ.IsAddHaarMeasure] [μ.Regular] in

private theorem mulMeasure_eq_of_subset_smul_shell (hϖ : Irreducible ϖ)
    (w : (v.adicCompletion F)ˣ) {S : Set (v.adicCompletion F)} (hS : MeasurableSet S)
    (hsub : S ⊆ (w : v.adicCompletion F) • shellSet hϖ 0) :
    mulMeasure μ S = ((modulus (w : v.adicCompletion F) : ℝ≥0∞))⁻¹ * μ S := by
  have hmod : ∀ x ∈ S, modulus x = modulus (w : v.adicCompletion F) := by
    intro x hx
    rcases hsub hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    show modulus ((w : v.adicCompletion F) • y) = modulus (w : v.adicCompletion F)
    have hval : (w : v.adicCompletion F) • y
        = ((w * Units.mk0 y hy0 : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp [smul_eq_mul]
    rw [hval, modulus_coe_units, map_mul]
    have h1 : distribHaarChar (v.adicCompletion F) (Units.mk0 y hy0) = 1 := by
      rw [LocalHaarModulus.distribHaarChar_adicCompletion,
        (mem_shellSet_iff_ord_eq hϖ 0 hy0).mp hy]
      simp
    rw [h1, mul_one, ← modulus_coe_units]
  have hS0 : S ⊆ {(0 : v.adicCompletion F)}ᶜ := by
    intro x hx
    rcases hsub hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
    exact mul_ne_zero w.ne_zero hy0
  rw [mulMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hS0,
    setLIntegral_congr_fun hS (fun x hx => by rw [hmod x hx]),
    setLIntegral_const]

private theorem measure_units_smul (u : (v.adicCompletion F)ˣ) (S : Set (v.adicCompletion F)) :
    μ ((u : v.adicCompletion F) • S)
      = (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ S := by
  rw [distribHaarChar_mul]
  rfl

private theorem mulMeasure_units_smul (hϖ : Irreducible ϖ) (u : (v.adicCompletion F)ˣ)
    {T : Set (v.adicCompletion F)} (hT : MeasurableSet T)
    (hT0 : T ⊆ {(0 : v.adicCompletion F)}ᶜ) :
    mulMeasure μ ((u : v.adicCompletion F) • T) = mulMeasure μ T := by
  classical
  have hTdec : T = ⋃ k : ℤ, T ∩ genShell hϖ k := by
    rw [← Set.inter_iUnion, iUnion_genShell hϖ, Set.inter_eq_left.mpr hT0]
  have hmeasT : ∀ k : ℤ, MeasurableSet (T ∩ genShell hϖ k) :=
    fun k => hT.inter (measurableSet_genShell hϖ k)
  have hdisT : Pairwise (Function.onFun Disjoint (fun k => T ∩ genShell hϖ k)) :=
    fun _ _ hkl => ((genShell_disjoint hϖ hkl).mono inter_subset_right inter_subset_right)
  have hudec : (u : v.adicCompletion F) • T
      = ⋃ k : ℤ, (u : v.adicCompletion F) • (T ∩ genShell hϖ k) := by
    conv_lhs => rw [hTdec]
    rw [Set.smul_set_iUnion]
  have hmeasU : ∀ k : ℤ, MeasurableSet ((u : v.adicCompletion F) • (T ∩ genShell hϖ k)) :=
    fun k => measurableSet_smul_set u.ne_zero (hmeasT k)
  have hdisU : Pairwise
      (Function.onFun Disjoint (fun k => (u : v.adicCompletion F) • (T ∩ genShell hϖ k))) := by
    intro k l hkl
    rw [Function.onFun, smul_set_eq_preimage u.ne_zero, smul_set_eq_preimage u.ne_zero]
    exact (hdisT hkl).preimage _
  have hper : ∀ k : ℤ, mulMeasure μ ((u : v.adicCompletion F) • (T ∩ genShell hϖ k))
      = mulMeasure μ (T ∩ genShell hϖ k) := by
    intro k
    set w : (v.adicCompletion F)ˣ := piUnit hϖ ^ k with hw
    have hsub₁ : T ∩ genShell hϖ k ⊆ (w : v.adicCompletion F) • shellSet hϖ 0 :=
      fun x hx => hx.2
    have hsub₂ : (u : v.adicCompletion F) • (T ∩ genShell hϖ k)
        ⊆ ((u * w : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0 := by
      rintro x ⟨y, hy, rfl⟩
      rcases hsub₁ hy with ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [smul_eq_mul, mul_assoc]⟩
    rw [mulMeasure_eq_of_subset_smul_shell μ hϖ (u * w) (hmeasU k) hsub₂,
      mulMeasure_eq_of_subset_smul_shell μ hϖ w (hmeasT k) hsub₁,
      measure_units_smul μ u]
    rw [modulus_coe_units, modulus_coe_units, map_mul]
    have hu0 : (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne'
    have huT : (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hu0) (Or.inl huT)]
    calc (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)⁻¹
          * (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹
          * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ (T ∩ genShell hϖ k))
        = (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹
          * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)⁻¹
            * (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)) * μ (T ∩ genShell hϖ k) := by
          ring
      _ = (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹ * μ (T ∩ genShell hϖ k) := by
          rw [ENNReal.inv_mul_cancel hu0 huT, mul_one]
  rw [hudec, measure_iUnion hdisU hmeasU]
  conv_rhs => rw [hTdec, measure_iUnion hdisT hmeasT]
  exact tsum_congr hper

variable [MeasurableSpace ((v.adicCompletion F)ˣ)] [BorelSpace ((v.adicCompletion F)ˣ)]

private theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
  isOpenEmbedding_val.measurableEmbedding

private def mulHaar : Measure (v.adicCompletion F)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

omit [μ.IsAddHaarMeasure] [μ.Regular] in
private theorem mulHaar_apply {A : Set (v.adicCompletion F)ˣ} (hA : MeasurableSet A) :
    mulHaar μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => measurableEmbedding_val.measurableSet_image' hs) _ hA

private theorem isMulLeftInvariant_mulHaar (hϖ : Irreducible ϖ) :
    (mulHaar μ).IsMulLeftInvariant := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  have hpre : (fun h => g * h) ⁻¹' A = g⁻¹ • A := by
    ext a
    simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hApre : MeasurableSet ((fun h => g * h) ⁻¹' A) :=
    hA.preimage (measurable_const_mul g)
  rw [hpre] at hApre ⊢
  rw [mulHaar_apply μ hApre, mulHaar_apply μ hA, image_val_smul]
  exact mulMeasure_units_smul μ hϖ g⁻¹ (measurableEmbedding_val.measurableSet_image' hA)
    (image_val_subset_compl_zero A)

private theorem isFiniteMeasureOnCompacts_mulHaar (hϖ : Irreducible ϖ) :
    IsFiniteMeasureOnCompacts (mulHaar μ) := by
  haveI hT2 : T2Space ((v.adicCompletion F)ˣ) := Units.isEmbedding_val₀.t2Space
  constructor
  intro C hC
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  rw [mulHaar_apply μ hCm]
  have hC' : IsCompact (Units.val '' C) := hC.image Units.isEmbedding_val₀.continuous
  have hC'0 : (Units.val '' C) ⊆ {(0 : v.adicCompletion F)}ᶜ := image_val_subset_compl_zero C
  have hcov : (Units.val '' C) ⊆ ⋃ x : Units.val '' C,
      ((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2) : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) • shellSet hϖ 0 := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, 1, one_mem_shellSet_zero hϖ, ?_⟩
    simp [smul_eq_mul]
  have hopen : ∀ x : Units.val '' C, IsOpen
      (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2) : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) • shellSet hϖ 0) :=
    fun _ => isOpen_smul_set (Units.ne_zero _) (isOpen_shellSet hϖ 0)
  obtain ⟨t, ht⟩ := hC'.elim_finite_subcover _ hopen hcov
  calc mulMeasure μ (Units.val '' C)
      ≤ mulMeasure μ (⋃ x ∈ t,
          (Units.val '' C) ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
            : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) := by
        refine measure_mono fun y hy => ?_
        rcases Set.mem_iUnion₂.mp (ht hy) with ⟨x, hxt, hyx⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, hy, hyx⟩
    _ ≤ ∑ x ∈ t, mulMeasure μ ((Units.val '' C)
          ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
            : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) :=
        measure_biUnion_finset_le _ _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.mpr fun x _ => ?_
        have hmeas : MeasurableSet ((Units.val '' C)
            ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
              : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) :=
          (hC'.isClosed.measurableSet).inter
            (measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0))
        rw [mulMeasure_eq_of_subset_smul_shell μ hϖ _ hmeas inter_subset_right]
        refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ?_) ?_
        · rw [modulus_coe_units]
          exact ENNReal.coe_pos.mpr distribHaarChar_pos
        · refine lt_of_le_of_lt (measure_mono (inter_subset_right.trans
            (Set.smul_set_mono (shellSet_subset_integers hϖ 0)))) ?_
          rw [LocalHaarModulus.measure_smul_integers μ]
          exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_integers_lt_top μ)

omit [μ.Regular] in

private theorem isOpenPosMeasure_mulHaar (hϖ : Irreducible ϖ) :
    (mulHaar μ).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [mulHaar_apply μ hU.measurableSet]
  obtain ⟨u₀, hu₀⟩ := hUne
  have hUim : IsOpen (Units.val '' U) := isOpenEmbedding_val.isOpenMap _ hU
  have hWopen : IsOpen ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)) :=
    hUim.inter (isOpen_smul_set (Units.ne_zero _) (isOpen_shellSet hϖ 0))
  have hWne : ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)).Nonempty := by
    refine ⟨(u₀ : v.adicCompletion F), ⟨u₀, hu₀, rfl⟩, 1, one_mem_shellSet_zero hϖ, ?_⟩
    simp [smul_eq_mul]
  have hWpos : 0 < mulMeasure μ ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)) := by
    rw [mulMeasure_eq_of_subset_smul_shell μ hϖ u₀ hWopen.measurableSet inter_subset_right]
    refine ENNReal.mul_pos ?_ (hWopen.measure_pos μ hWne).ne'
    exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  exact (hWpos.trans_le (measure_mono inter_subset_left)).ne'

private theorem isHaarMeasure_mulHaar (hϖ : Irreducible ϖ) : (mulHaar μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaar μ hϖ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaar μ hϖ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaar μ hϖ }

end MulHaarFromAdditive
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_MulHaarFromAdditive
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section FinGKFold_ValuedOrdBridge

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open WithZero Multiplicative
open scoped NNReal ENNReal

noncomputable section

namespace M4aP2DGK
namespace FinGK
namespace ValuedOrdBridge

open LocalZetaUnramified MulHaarFromAdditive

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem valued_ne_zero_of_ne_zero {x : v.adicCompletion F} (hx : x ≠ 0) :
    Valued.v x ≠ 0 := by
  intro h0
  have h1 : Valued.v x * Valued.v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

private theorem valued_le_one_of_mem {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v x ≤ 1 :=
  hx

private theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Integers (v.adicCompletionIntegers F) :=
  Valuation.valuationSubring.integers _

private theorem exists_irreducible_valued :
    ∃ ϖ : v.adicCompletionIntegers F, Irreducible ϖ ∧
      Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
        = WithZero.exp (-1 : ℤ) := by
  obtain ⟨y, hy⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp (-1 : ℤ))
  have hy1 : y ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, hy, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  refine ⟨⟨y, hy1⟩, ⟨?_, ?_⟩, hy⟩
  ·
    intro hu
    have h1 := (integers_adicCompletionIntegers (v := v)).one_of_isUnit hu
    rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) ⟨y, hy1⟩ = y
      from rfl, hy] at h1
    exact absurd ((WithZero.exp_eq_one).mp h1) (by norm_num)
  ·
    rintro a b hab
    have hane : (a : v.adicCompletion F) ≠ 0 := by
      intro h0
      apply hy0
      have : y = (a : v.adicCompletion F) * (b : v.adicCompletion F) := by
        simpa using congrArg Subtype.val hab
      rw [this, h0, zero_mul]
    have hbne : (b : v.adicCompletion F) ≠ 0 := by
      intro h0
      apply hy0
      have : y = (a : v.adicCompletion F) * (b : v.adicCompletion F) := by
        simpa using congrArg Subtype.val hab
      rw [this, h0, mul_zero]
    have hmul : Valued.v ((a : v.adicCompletion F)) * Valued.v ((b : v.adicCompletion F))
        = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul]
      have : (a : v.adicCompletion F) * (b : v.adicCompletion F) = y := by
        simpa using (congrArg Subtype.val hab).symm
      rw [this, hy]
    have hva0 : Valued.v ((a : v.adicCompletion F)) ≠ 0 := by
      exact valued_ne_zero_of_ne_zero hane
    have hvb0 : Valued.v ((b : v.adicCompletion F)) ≠ 0 := by
      exact valued_ne_zero_of_ne_zero hbne
    set s : ℤ := WithZero.log (Valued.v ((a : v.adicCompletion F))) with hs
    set t : ℤ := WithZero.log (Valued.v ((b : v.adicCompletion F))) with ht
    have hexps : Valued.v ((a : v.adicCompletion F)) = WithZero.exp s :=
      (WithZero.exp_log hva0).symm
    have hexpt : Valued.v ((b : v.adicCompletion F)) = WithZero.exp t :=
      (WithZero.exp_log hvb0).symm
    have hsum : s + t = -1 := by
      have := hmul
      rw [hexps, hexpt, ← WithZero.exp_add] at this
      exact WithZero.exp_inj.mp this
    have hsle : s ≤ 0 := by
      have := valued_le_one_of_mem a.2
      rw [hexps, ← WithZero.exp_zero] at this
      exact WithZero.exp_le_exp.mp this
    have htle : t ≤ 0 := by
      have := valued_le_one_of_mem b.2
      rw [hexpt, ← WithZero.exp_zero] at this
      exact WithZero.exp_le_exp.mp this
    rcases (by omega : s = 0 ∨ t = 0) with h0 | h0
    · left
      refine (integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := a) ?_
      rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) a
        = (a : v.adicCompletion F) from rfl, hexps, h0, WithZero.exp_zero]
    · right
      refine (integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := b) ?_
      rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) b
        = (b : v.adicCompletion F) from rfl, hexpt, h0, WithZero.exp_zero]

variable {ϖ : v.adicCompletionIntegers F}

private theorem valued_coe_of_irreducible (hϖ : Irreducible ϖ) :
    Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀, hv₀⟩ := exists_irreducible_valued (v := v)

  have hϖK : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
    coe_ne_zero_of_irreducible hϖ
  have hϖv0 : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    exact valued_ne_zero_of_ne_zero hϖK
  have hle : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    valued_le_one_of_mem ϖ.2
  have hne1 : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := ϖ) h1)

  set s : ℤ := WithZero.log
    (Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)) with hs
  have hexps : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp s := (WithZero.exp_log hϖv0).symm
  have hsle : s ≤ 0 := by
    have := hle
    rw [hexps, ← WithZero.exp_zero] at this
    exact WithZero.exp_le_exp.mp this
  have hsne : s ≠ 0 := by
    intro h0
    exact hne1 (by rw [hexps, h0, WithZero.exp_zero])
  have hlev : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      ≤ Valued.v ((π₀ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hexps, hv₀]
    exact WithZero.exp_le_exp.mpr (by omega)

  have hdvd : π₀ ∣ ϖ :=
    ((integers_adicCompletionIntegers (v := v)).le_iff_dvd (x := ϖ) (y := π₀)).mp hlev
  obtain ⟨c, hc⟩ := hdvd
  rcases hϖ.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu hπ₀.not_isUnit
  · have h1 : Valued.v ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      have := (integers_adicCompletionIntegers (v := v)).one_of_isUnit hu
      rwa [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) c
        = (c : v.adicCompletion F) from rfl] at this
    have hcoe : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
        = ((π₀ : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((c : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      simpa using congrArg Subtype.val hc
    rw [hcoe, map_mul, hv₀, h1, mul_one]

private theorem valued_coe_units_eq_exp_neg_ord (x : (v.adicCompletion F)ˣ) :
    Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) := by
  obtain ⟨π₀, hπ₀, hv₀⟩ := exists_irreducible_valued (v := v)
  set n : ℤ := ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) with hn
  set u : (v.adicCompletion F)ˣ := (piUnit hπ₀ ^ n)⁻¹ * x with hu
  have hordu : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0 := by
    rw [hu, ord_ofMul_mul,
      show ((piUnit hπ₀ ^ n)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hπ₀ ^ (-n) from
        (zpow_neg _ _).symm,
      ord_ofMul_zpow_piUnit hπ₀, ← hn]
    omega

  obtain ⟨w, hw⟩ := (ValuationOrd.ord_eq_zero_iff (v.adicCompletionIntegers F) u).mp hordu
  have hvu : Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    have hiso : ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (w : _) := by
      rw [← hw]; rfl
    rw [hiso]
    exact (integers_adicCompletionIntegers (v := v)).one_of_isUnit w.isUnit

  have hx : (x : (v.adicCompletion F)ˣ) = piUnit hπ₀ ^ n * u := by
    rw [hu, mul_inv_cancel_left]
  have hvpi : Valued.v (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
      = WithZero.exp (-n) := by
    have hzpow : (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
        = (((piUnit hπ₀ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) ^ n := by
      push_cast
      rfl
    rw [hzpow, map_zpow₀, piUnit_val, valued_coe_of_irreducible hπ₀,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]
  calc Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = Valued.v ((((piUnit hπ₀ ^ n * u : (v.adicCompletion F)ˣ)) : v.adicCompletion F)) := by
        rw [← hx]
    _ = Valued.v (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
        * Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
        rw [Units.val_mul, map_mul]
    _ = WithZero.exp (-n) := by rw [hvpi, hvu, mul_one]

private theorem coe_mem_integers_iff_ord_nonneg (x : (v.adicCompletion F)ˣ) :
    ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      ↔ 0 ≤ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) := by
  rw [mem_adicCompletionIntegers, valued_coe_units_eq_exp_neg_ord, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

end ValuedOrdBridge
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_ValuedOrdBridge
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section FinGKFold_WeylGK

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aP2DGK
namespace FinGK
namespace WeylGK

open LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem ord_eq_one_of_valued (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v ((ϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ) = 1 := by
  have h := valued_coe_units_eq_exp_neg_ord ϖ
  rw [hϖ] at h
  have h' : WithZero.exp (-1 : ℤ)
      = WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ))) := h
  have h'' := WithZero.exp_injective h'
  omega

variable {χ : (v.adicCompletion F)ˣ →* ℂˣ}

variable {π : v.adicCompletionIntegers F}

private def negShell (hπ : Irreducible π) (m : ℕ) : Set (v.adicCompletion F) :=
  genShell hπ (-((m : ℤ) + 1))

private theorem ne_zero_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) : x ≠ 0 := by
  have h : x ∈ ⋃ k : ℤ, genShell hπ k := Set.mem_iUnion.mpr ⟨_, hx⟩
  rw [iUnion_genShell hπ] at h
  exact h

private theorem ord_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) (hx0 : x ≠ 0) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx0)) = -((m : ℤ) + 1) :=
  (mem_genShell_iff hπ hx0).mp hx

private theorem compl_integers_eq_iUnion_negShell (hπ : Irreducible π) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ = ⋃ m : ℕ, negShell hπ m := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hxO
    have hx0 : x ≠ 0 := by
      intro h0
      exact hxO (h0 ▸ (v.adicCompletionIntegers F).zero_mem)
    have hord : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx0)) < 0 := by
      by_contra hge
      exact hxO ((coe_mem_integers_iff_ord_nonneg (Units.mk0 x hx0)).mpr (not_lt.mp hge))
    refine ⟨(-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx0))) - 1).toNat,
      (mem_genShell_iff hπ hx0).mpr ?_⟩
    omega
  · rintro ⟨m, hm⟩ hxO
    have hx0 : x ≠ 0 := ne_zero_of_mem_negShell hπ hm
    have h1 := ord_of_mem_negShell hπ hm hx0
    have h2 := (coe_mem_integers_iff_ord_nonneg (Units.mk0 x hx0)).mp hxO
    omega

private theorem negShell_disjoint (hπ : Irreducible π) :
    Pairwise (Function.onFun Disjoint (negShell hπ)) := by
  intro m m' hmm'
  have h : (-((m : ℤ) + 1)) ≠ (-((m' : ℤ) + 1)) := by
    intro h
    apply hmm'
    omega
  exact genShell_disjoint hπ h

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

private theorem measurableSet_negShell (hπ : Irreducible π) (m : ℕ) : MeasurableSet (negShell hπ m) :=
  measurableSet_genShell hπ _

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end WeylGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_WeylGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section FinGKFold_Main

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aP2DGK
namespace FinGK
namespace WeylGK

open LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge

end WeylGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_Main
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section SmoothShell_Main

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set Filter Topology
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace LocalIntertwining
namespace SmoothShell

open M4aP2DGK.FinGK M4aP2DGK.FinGK.LocalZetaUnramified M4aP2DGK.FinGK.MulHaarFromAdditive
open M4aP2DGK.FinGK.ValuedOrdBridge M4aP2DGK.FinGK.WeylGK

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

section SetBridges

variable {π : v.adicCompletionIntegers F}

private theorem zero_notMem_genShell (hπ : Irreducible π) (k : ℤ) :
    (0 : v.adicCompletion F) ∉ genShell hπ k := by
  rintro ⟨y, hy, h0⟩
  have h0' : ((piUnit hπ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y = 0 := h0
  have hy0 : y = 0 := by
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  exact zero_notMem_shellSet hπ 0 (hy0 ▸ hy)

private theorem genShell_subset_compl_zero (hπ : Irreducible π) (k : ℤ) :
    genShell hπ k ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx h0
  rw [Set.mem_singleton_iff] at h0
  exact zero_notMem_genShell hπ k (h0 ▸ hx)

private theorem setOf_valued_eq_genShell (hπ : Irreducible π) (k : ℤ) :
    {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd k : Multiplicative ℤ)}
      = genShell hπ (-k) := by
  ext x
  simp only [Set.mem_setOf_eq]
  by_cases hx : x = 0
  · subst hx
    rw [map_zero]
    constructor
    · intro h
      exact absurd h.symm WithZero.coe_ne_zero
    · intro h
      exact absurd h (zero_notMem_genShell hπ (-k))
  · rw [mem_genShell_iff hπ hx]
    have hv : Valued.v x = WithZero.exp
        (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx)))) :=
      valued_coe_units_eq_exp_neg_ord (Units.mk0 x hx)
    rw [hv, show ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        = WithZero.exp k from rfl, WithZero.exp_inj]
    omega

private theorem setOf_valued_eq_one_eq_genShell (hπ : Irreducible π) :
    {u : v.adicCompletion F | Valued.v u = 1} = genShell hπ 0 := by
  have h := setOf_valued_eq_genShell hπ 0
  rw [neg_zero] at h
  rw [← h]
  ext u
  simp only [Set.mem_setOf_eq, ofAdd_zero, WithZero.coe_one]

private theorem genShell_zero_eq (hπ : Irreducible π) : genShell hπ 0 = shellSet hπ 0 := by
  rw [genShell, zpow_zero, Units.val_one, one_smul]

private theorem smul_shellSet_zero_of_ord_eq_zero (hπ : Irreducible π) (w : (v.adicCompletion F)ˣ)
    (hw : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0) :
    (w : v.adicCompletion F) • shellSet hπ 0 = shellSet hπ 0 := by
  have key : ∀ w : (v.adicCompletion F)ˣ,
      ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 →
        (w : v.adicCompletion F) • shellSet hπ 0 ⊆ shellSet hπ 0 := by
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hπ 0 (h ▸ hy)
    have hx0 : (w : v.adicCompletion F) • y ≠ 0 := by
      rw [smul_eq_mul]
      exact mul_ne_zero (Units.ne_zero _) hy0
    refine (mem_shellSet_iff_ord_eq hπ 0 hx0).mpr ?_
    have hmk : Units.mk0 ((w : v.adicCompletion F) • y) hx0 = w * Units.mk0 y hy0 :=
      Units.ext (by simp [smul_eq_mul])
    rw [hmk, ord_ofMul_mul, hw, (mem_shellSet_iff_ord_eq hπ 0 hy0).mp hy]
    simp
  refine Set.Subset.antisymm (key w hw) ?_
  intro x hx
  have hw' : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w⁻¹) = 0 := by
    have h := ord_ofMul_mul w w⁻¹
    rw [mul_inv_cancel, hw, zero_add] at h
    rw [← h]
    exact map_zero _
  refine ⟨((w⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • x, key w⁻¹ hw' ⟨x, hx, rfl⟩, ?_⟩
  show (w : v.adicCompletion F) • (((w⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • x) = x
  rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

private theorem genShell_neg_eq_smul (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    genShell hπ (-(n : ℤ)) = ((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) • genShell hπ 0 := by
  rw [genShell_zero_eq]
  set w : (v.adicCompletion F)ˣ := (ϖ⁻¹ ^ n)⁻¹ * piUnit hπ ^ (-(n : ℤ)) with hw_def
  have hordϖ : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ) = 1 :=
    ord_eq_one_of_valued ϖ hϖ
  have hw : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
    rw [hw_def, ord_ofMul_mul, ord_ofMul_zpow_piUnit hπ, inv_pow, inv_inv]
    have h1 : Additive.ofMul (ϖ ^ n) = n • Additive.ofMul ϖ := rfl
    rw [h1, map_nsmul, hordϖ]
    simp
  have hfac : (piUnit hπ ^ (-(n : ℤ)) : (v.adicCompletion F)ˣ) = (ϖ⁻¹ ^ n) * w := by
    rw [hw_def, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [genShell, hfac, Units.val_mul, mul_smul, smul_shellSet_zero_of_ord_eq_zero hπ w hw]

private theorem isCompact_shellSet_zero (hπ : Irreducible π) : IsCompact (shellSet hπ 0) := by
  unfold shellSet
  exact IsCompact.diff (isCompact_smul_integers _)
    ((NumberField.isOpenAdicCompletionIntegers F v).smul₀ (Units.ne_zero _))

private theorem isCompact_genShell (hπ : Irreducible π) (k : ℤ) : IsCompact (genShell hπ k) := by
  unfold genShell
  exact IsCompact.smul _ (isCompact_shellSet_zero hπ)

private theorem ord_inv_pow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ⁻¹ ^ n)) = -(n : ℤ) := by
  rw [inv_pow]
  have h1 : Additive.ofMul ((ϖ ^ n)⁻¹) = -(n • Additive.ofMul ϖ) := rfl
  rw [h1, map_neg, map_nsmul, ord_eq_one_of_valued ϖ hϖ]
  simp

private theorem distribHaarChar_inv_pow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    distribHaarChar (v.adicCompletion F) (ϖ⁻¹ ^ n) = normQ v ^ n := by
  rw [LocalHaarModulus.distribHaarChar_adicCompletion, ord_inv_pow ϖ hϖ n, neg_neg, zpow_natCast]

private theorem modulus_inv_pow_mul (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ)
    {u : v.adicCompletion F} (hu : u ∈ genShell hπ 0) :
    modulus (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) = normQ v ^ n := by
  have hu0 : u ≠ 0 := fun h => zero_notMem_genShell hπ 0 (h ▸ hu)
  have hx0 : ((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) hu0
  rw [modulus_of_ne_zero_adicCompletion hx0]
  have hmk : Units.mk0 _ hx0 = ϖ⁻¹ ^ n * Units.mk0 u hu0 := Units.ext (by simp)
  have hordu : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 u hu0)) = 0 :=
    (mem_genShell_iff hπ hu0).mp hu
  rw [hmk, ord_ofMul_mul, hordu, add_zero, ord_inv_pow ϖ hϖ n, neg_neg, zpow_natCast]

private theorem modulus_of_mem_genShell (hπ : Irreducible π) {k : ℤ} {x : v.adicCompletion F}
    (hx : x ∈ genShell hπ k) : modulus x = normQ v ^ (-k) := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_genShell hπ k (h ▸ hx)
  rw [modulus_of_ne_zero_adicCompletion hx0, (mem_genShell_iff hπ hx0).mp hx]

end SetBridges
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section Substitution

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem setIntegral_units_smul (u : (v.adicCompletion F)ˣ) {S : Set (v.adicCompletion F)}
    (hS : MeasurableSet S) (f : v.adicCompletion F → E) :
    ∫ x in (u : v.adicCompletion F) • S, f x ∂μ
      = ((distribHaarChar (v.adicCompletion F) u : ℝ≥0) : ℝ)
          • ∫ y in S, f ((u : v.adicCompletion F) * y) ∂μ := by
  set T : v.adicCompletion F ≃ᵐ v.adicCompletion F :=
    MeasurableEquiv.mulLeft₀ (u : v.adicCompletion F) u.ne_zero with hT
  have hTapply : (T : v.adicCompletion F → v.adicCompletion F) = fun y => (u : v.adicCompletion F) * y := rfl
  set Δ : ℝ≥0 := distribHaarChar (v.adicCompletion F) u with hΔ
  have hΔ0 : Δ ≠ 0 := (distribHaarChar_pos).ne'
  have hΔinv : distribHaarChar (v.adicCompletion F) u⁻¹ = Δ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hΔ, ← map_mul, inv_mul_cancel, map_one]
  have hpre : ∀ A : Set (v.adicCompletion F),
      T ⁻¹' A = ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) • A := by
    intro A
    ext y
    simp only [Set.mem_preimage, hTapply]
    constructor
    · intro hy
      exact ⟨(u : v.adicCompletion F) * y, hy, by simp [smul_eq_mul]⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [smul_eq_mul] using hz
  have hmap : Measure.map T μ = ((Δ : ℝ≥0∞))⁻¹ • μ := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply T.measurable hA, Measure.smul_apply, smul_eq_mul, hpre A,
      measure_units_smul μ u⁻¹ A, hΔinv, ENNReal.coe_inv hΔ0]
  have hmeas : MeasurableSet ((u : v.adicCompletion F) • S) := measurableSet_smul_set u.ne_zero hS
  have hpreS : T ⁻¹' ((u : v.adicCompletion F) • S) = S := by
    rw [hpre, smul_smul, Units.inv_mul, one_smul]
  have hind : ∀ y, S.indicator (fun y => f ((u : v.adicCompletion F) * y)) y
      = ((u : v.adicCompletion F) • S).indicator f (T y) := by
    intro y
    have hmemiff : y ∈ S ↔ T y ∈ (u : v.adicCompletion F) • S := by
      rw [← Set.mem_preimage, hpreS]
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hmemiff.mp hy), hTapply]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hmemiff.mpr h))]
  have key : ∫ y in S, f ((u : v.adicCompletion F) * y) ∂μ
      = (((Δ : ℝ≥0∞))⁻¹).toReal • ∫ x in (u : v.adicCompletion F) • S, f x ∂μ := by
    rw [← integral_indicator hS, ← integral_indicator hmeas, ← integral_smul_measure, ← hmap,
      integral_map_equiv]
    exact integral_congr_ae (Eventually.of_forall hind)
  rw [key, ENNReal.toReal_inv, ENNReal.coe_toReal, smul_smul, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hΔ0),
    one_smul]

end Substitution
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section Regularity

private theorem setOf_valued_sub_le_mem_nhds (x z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w ≤ Valued.v.restrict z} :=
    Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) ≤ Valued.v.restrict z} := by
    simp
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_setOf_eq, Valuation.restrict_le_iff] at hy
  exact hy

private theorem setOf_valued_sub_lt_mem_nhds (x z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    {y : v.adicCompletion F | Valued.v (y - x) < Valued.v z} ∈ 𝓝 x := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have hopen : IsOpen {w : v.adicCompletion F | Valued.v.restrict w < Valued.v.restrict z} :=
    Valued.isOpen_ball (R := v.adicCompletion F) _
  have hopen' : IsOpen {y : v.adicCompletion F | Valued.v.restrict (y - x) < Valued.v.restrict z} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : v.adicCompletion F | Valued.v.restrict (y - x) < Valued.v.restrict z} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact pos_iff_ne_zero.mpr hr
  refine Filter.mem_of_superset (hopen'.mem_nhds hx) fun y hy => ?_
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff] at hy
  exact hy

private theorem continuous_of_depth (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    Continuous B := by
  obtain ⟨π, -, hπv⟩ := exists_irreducible_valued (v := v)
  have hz : Valued.v (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ m)
      = (Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) := by
    rw [map_pow, hπv, ← WithZero.exp_nsmul]
    simp [WithZero.exp]
  have hz0 : Valued.v (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ m) ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_le_mem_nhds x _ hz0] with y hy
  rw [hz] at hy
  exact (hB x y hy).symm

private theorem apply_inv_eq_apply_zero_of_depth (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) {x : v.adicCompletion F}
    (hx : Valued.v x = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ)) :
    B x⁻¹ = B 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.coe_ne_zero hx.symm
  refine hB 0 x⁻¹ ?_
  rw [sub_zero, map_inv₀, hx,
    show ((Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      = WithZero.exp (n : ℤ) from rfl, ← WithZero.exp_neg,
    show ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      = WithZero.exp (-(m : ℤ)) from rfl, WithZero.exp_le_exp]
  omega

private theorem continuousOn_charExt_inv (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ higherUnitsAt F v c, χ u = 1) :
    ContinuousOn (charExt χ⁻¹) {(0 : v.adicCompletion F)}ᶜ := by
  obtain ⟨c, hc⟩ := hχ
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨π, -, hπv⟩ := exists_irreducible_valued (v := v)
  have hzv : Valued.v (x * (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c))
      = Valued.v x * WithZero.exp (-(c : ℤ)) := by
    rw [map_mul, map_pow, hπv, ← WithZero.exp_nsmul]
    simp
  have hz0 : Valued.v (x * (((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ c)) ≠ 0 := by
    rw [hzv]
    exact mul_ne_zero hvx WithZero.coe_ne_zero
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_lt_mem_nhds x _ hz0] with y hy
  rw [hzv] at hy
  have hyle := hy.le
  have hle1 : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hlt : Valued.v (y - x) < Valued.v x :=
    lt_of_lt_of_le hy (mul_le_of_le_one_right' hle1)
  have hvy : Valued.v y = Valued.v x := Valuation.map_eq_of_sub_lt _ hlt
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hvy
    exact hvx hvy.symm
  set u : (v.adicCompletion F)ˣ := (Units.mk0 x hx)⁻¹ * Units.mk0 y hy0 with hu
  have huval : (u : v.adicCompletion F) = x⁻¹ * y := by simp [hu]
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := by
    rw [huval, map_mul, map_inv₀, hvy, inv_mul_cancel₀ hvx]
  have hu2 : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
    have h1 : (u : v.adicCompletion F) - 1 = x⁻¹ * (y - x) := by
      rw [huval, mul_sub, inv_mul_cancel₀ hx]
    rw [h1, map_mul, map_inv₀]
    calc (Valued.v x)⁻¹ * Valued.v (y - x)
        ≤ (Valued.v x)⁻¹ * (Valued.v x * WithZero.exp (-(c : ℤ))) := by gcongr
      _ = WithZero.exp (-(c : ℤ)) := by rw [← mul_assoc, inv_mul_cancel₀ hvx, one_mul]
  have hmem : u ∈ higherUnitsAt F v c := ⟨hu1, Or.inr hu2⟩
  have hχu : χ u = 1 := hc u hmem
  have hy' : Units.mk0 y hy0 = Units.mk0 x hx * u := by
    rw [hu, ← mul_assoc, mul_inv_cancel, one_mul]
  show charExt χ⁻¹ x = charExt χ⁻¹ y
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy0, hy', map_mul]
  simp [hχu]

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
variable {π : v.adicCompletionIntegers F}

omit [μ.Regular] in

private theorem integrableOn_genShell (hπ : Irreducible π) (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ higherUnitsAt F v c, χ u = 1) (w : ℂ) (m : ℕ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) (k : ℤ) :
    IntegrableOn (fun x => charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w * B x⁻¹) (genShell hπ k) μ := by
  have hcont : ContinuousOn (fun x => charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w * B x⁻¹)
      (genShell hπ k) := by
    have h0 := genShell_subset_compl_zero hπ k
    have hc : ContinuousOn (fun x : v.adicCompletion F => ((((normQ v ^ (-k) : ℝ≥0) : ℝ)) : ℂ) ^ w)
        (genShell hπ k) := continuousOn_const
    have hmod : ContinuousOn (fun x : v.adicCompletion F => (((modulus x : ℝ)) : ℂ) ^ w) (genShell hπ k) :=
      hc.congr (fun x hx => by simp only [modulus_of_mem_genShell hπ hx])
    have hB' : ContinuousOn (fun x : v.adicCompletion F => B x⁻¹) (genShell hπ k) :=
      (continuous_of_depth m B hB).comp_continuousOn (continuousOn_inv₀.mono h0)
    exact (((continuousOn_charExt_inv χ hχ).mono h0).mul hmod).mul hB'
  exact hcont.integrableOn_compact (isCompact_genShell hπ k)

end Regularity
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section Tail

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]
variable {π : v.adicCompletionIntegers F}

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
private theorem normQ_pos : (0 : ℝ) < ((normQ v : ℝ≥0) : ℝ) := by
  exact_mod_cast lt_of_lt_of_le one_pos (one_le_normQ (v := v))

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in

private theorem integrand_inv_pow_mul (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (w : ℂ) (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) {u : v.adicCompletion F} (hu : u ∈ genShell hπ 0) :
    charExt χ⁻¹ (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u)
        * (((modulus (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u) : ℝ)) : ℂ) ^ w
        * B (((ϖ⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * u)⁻¹
      = (((χ ϖ : ℂˣ) : ℂ) ^ n * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ w) ^ n * B 0) * charExt χ⁻¹ u := by
  set c : (v.adicCompletion F)ˣ := ϖ⁻¹ ^ n with hc
  have hu0 : u ≠ 0 := fun h => zero_notMem_genShell hπ 0 (h ▸ hu)
  have hx0 : (c : v.adicCompletion F) * u ≠ 0 := mul_ne_zero (Units.ne_zero _) hu0

  have hchar : charExt χ⁻¹ ((c : v.adicCompletion F) * u) = ((χ ϖ : ℂˣ) : ℂ) ^ n * charExt χ⁻¹ u := by
    have hmk : Units.mk0 _ hx0 = c * Units.mk0 u hu0 := Units.ext (by simp)
    rw [charExt_of_ne_zero _ hx0, charExt_of_ne_zero _ hu0, hmk, map_mul, hc]
    simp [map_pow]

  have hmod : (((modulus ((c : v.adicCompletion F) * u) : ℝ)) : ℂ) ^ w
      = ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ w) ^ n := by
    rw [hc, modulus_inv_pow_mul hπ ϖ hϖ n hu, NNReal.coe_pow, ofReal_pow_cpow (normQ_pos (v := v)).le]

  have hval : Valued.v ((c : v.adicCompletion F) * u) = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) := by
    have hmem : (c : v.adicCompletion F) * u
        ∈ {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ)} := by
      rw [setOf_valued_eq_genShell hπ (n : ℤ), genShell_neg_eq_smul hπ ϖ hϖ n, ← hc]
      exact Set.smul_mem_smul_set hu
    exact hmem
  have hBval : B ((c : v.adicCompletion F) * u)⁻¹ = B 0 := apply_inv_eq_apply_zero_of_depth m B hB hmn hval
  rw [hchar, hmod, hBval]
  ring

private theorem setIntegral_tailShell (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) :
    ∫ x in genShell hπ (-(n : ℤ)), charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹ ∂μ
      = B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ)
          * ((((χ ϖ : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s))) ^ n) := by
  have hN0 : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (normQ_pos (v := v)).ne'
  rw [genShell_neg_eq_smul hπ ϖ hϖ n, setIntegral_units_smul μ (ϖ⁻¹ ^ n) (measurableSet_genShell hπ 0),
    distribHaarChar_inv_pow ϖ hϖ n, Complex.real_smul,
    setIntegral_congr_fun (measurableSet_genShell hπ 0)
      (fun u hu => integrand_inv_pow_mul hπ ϖ hϖ χ (-(2 * s + 1)) m B hB hmn hu),
    integral_const_mul]
  have hpow : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1)) = ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s)) * ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
    rw [show (-(2 * s + 1) : ℂ) = -(2 * s) + (-1) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one]
  rw [hpow, NNReal.coe_pow, Complex.ofReal_pow, mul_pow]
  have hw : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ n * (((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  linear_combination (((χ ϖ : ℂˣ) : ℂ) ^ n * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s))) ^ n * B 0
    * ∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * hw

private theorem setIntegral_norm_tailShell (hπ : Irreducible π) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {n : ℕ} (hmn : m ≤ n) :
    ∫ x in genShell hπ (-(n : ℤ)), ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹‖ ∂μ
      = ‖B 0‖ * (∫ u in genShell hπ 0, ‖charExt χ⁻¹ u‖ ∂μ)
          * ‖((χ ϖ : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s))‖ ^ n := by
  have hN0 : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (normQ_pos (v := v)).ne'
  have hNpos : (0 : ℝ) < ((normQ v : ℝ≥0) : ℝ) := normQ_pos (v := v)
  rw [genShell_neg_eq_smul hπ ϖ hϖ n,
    setIntegral_units_smul μ (ϖ⁻¹ ^ n) (measurableSet_genShell hπ 0)
      (fun x => ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹‖),
    distribHaarChar_inv_pow ϖ hϖ n, smul_eq_mul,
    setIntegral_congr_fun (measurableSet_genShell hπ 0)
      (fun u hu => by
        show ‖_‖ = ‖((χ ϖ : ℂˣ) : ℂ) ^ n * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))) ^ n * B 0‖
            * ‖charExt χ⁻¹ u‖
        rw [integrand_inv_pow_mul hπ ϖ hϖ χ (-(2 * s + 1)) m B hB hmn hu, norm_mul]),
    integral_const_mul]

  have hpow : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1)) = ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s)) * ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
    rw [show (-(2 * s + 1) : ℂ) = -(2 * s) + (-1) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one]
  have hnormQ : ‖((((normQ v : ℝ≥0) : ℝ) : ℂ))‖ = (((normQ v : ℝ≥0) : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNpos.le]
  rw [hpow, NNReal.coe_pow]
  simp only [norm_mul, norm_pow, mul_pow, norm_inv, hnormQ]
  have hw : (((normQ v : ℝ≥0) : ℝ)) ^ n * ((((normQ v : ℝ≥0) : ℝ))⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  linear_combination (‖((χ ϖ : ℂˣ) : ℂ)‖ ^ n * ‖((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s)))‖ ^ n * ‖B 0‖
    * ∫ u in genShell hπ 0, ‖charExt χ⁻¹ u‖ ∂μ) * hw

omit [μ.IsAddHaarMeasure] [μ.Regular] in

private theorem setIntegral_lowShell (hπ : Irreducible π) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (B : v.adicCompletion F → ℂ) (n : ℕ) :
    ∫ x in genShell hπ (-(n : ℤ)), charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B x⁻¹ ∂μ
      = (((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1))) ^ n
          * ∫ x in genShell hπ (-(n : ℤ)), charExt χ⁻¹ x * B x⁻¹ ∂μ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_genShell hπ _) fun x hx => ?_
  rw [modulus_of_mem_genShell hπ hx, neg_neg, zpow_natCast, NNReal.coe_pow,
    ofReal_pow_cpow (normQ_pos (v := v)).le]
  ring

end Tail
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section Main

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem integral_smoothWeylIntegrand_impl
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x ∂μ)
        + (∑ n ∈ Finset.Ico 1 m,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ ∂μ)
        + B 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1}, LanglandsTunnell.TateLocal.charExt χ⁻¹ u ∂μ)
            * (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ m
            * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
  classical
  haveI : μ.Regular := inferInstance
  obtain ⟨π, hπ, -⟩ := exists_irreducible_valued (v := v)
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩

  set O : Set (v.adicCompletion F) := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hO
  set N : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) with hN
  set a : ℂ := ((χ ϖ : ℂˣ) : ℂ) * N ^ (-(2 * s)) with ha
  set g : v.adicCompletion F → ℂ :=
    fun y => charExt χ⁻¹ y * (((modulus y : ℝ)) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹ with hg
  have hQN : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) = N := by
    rw [hN, normQ]
    push_cast
    rfl
  have ha1 : ‖a‖ < 1 := hs
  have hns : ∀ k : ℕ, negShell hπ k = genShell hπ (-((k + 1 : ℕ) : ℤ)) := by
    intro k
    simp only [negShell, Nat.cast_add, Nat.cast_one]

  have hIntShell : ∀ k : ℕ, IntegrableOn g (negShell hπ k) μ := fun k =>
    integrableOn_genShell μ hπ χ hχ (-(2 * s + 1)) (m' + 1) B hB (-((k : ℤ) + 1))

  have htailval : ∀ k : ℕ, m' + 1 ≤ k + 1 → ∫ x in negShell hπ k, g x ∂μ
      = B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (k + 1) := by
    intro k hk
    rw [hns k, hg, setIntegral_tailShell μ hπ ϖ hϖ χ s (m' + 1) B hB hk, hQN]
  set C : ℝ := ‖B 0‖ * ∫ u in genShell hπ 0, ‖charExt χ⁻¹ u‖ ∂μ with hC
  have hnorm : ∀ k : ℕ, m' + 1 ≤ k + 1 → ∫ x in negShell hπ k, ‖g x‖ ∂μ = C * ‖a‖ ^ (k + 1) := by
    intro k hk
    rw [hns k, hg, setIntegral_norm_tailShell μ hπ ϖ hϖ χ s (m' + 1) B hB hk, hQN]

  have hlowval : ∀ k : ℕ, ∫ x in negShell hπ k, g x ∂μ
      = (N ^ (-(2 * s + 1))) ^ (k + 1)
        * ∫ x in {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd (((k + 1 : ℕ)) : ℤ) : Multiplicative ℤ)},
            charExt χ⁻¹ x * B x⁻¹ ∂μ := by
    intro k
    rw [hns k, hg, setIntegral_lowShell μ hπ χ s B (k + 1), hQN, setOf_valued_eq_genShell hπ]

  have hsum : Summable fun k : ℕ => ∫ x in negShell hπ k, ‖g x‖ ∂μ := by
    refine (summable_nat_add_iff m').mp ?_
    have h : (fun k : ℕ => ∫ x in negShell hπ (k + m'), ‖g x‖ ∂μ) = fun k => (C * ‖a‖ ^ (m' + 1)) * ‖a‖ ^ k := by
      funext k
      rw [hnorm (k + m') (by omega), show k + m' + 1 = (m' + 1) + k by ring, pow_add]
      ring
    rw [h]
    exact (summable_geometric_of_lt_one (norm_nonneg _) ha1).mul_left _
  have hOc : Oᶜ = ⋃ k : ℕ, negShell hπ k := compl_integers_eq_iUnion_negShell hπ
  have hInt : IntegrableOn g Oᶜ μ := by
    rw [hOc]
    exact integrableOn_iUnion_of_summable_integral_norm hIntShell hsum
  have hHas : HasSum (fun k : ℕ => ∫ x in negShell hπ k, g x ∂μ) (∫ x in Oᶜ, g x ∂μ) := by
    rw [hOc] at hInt ⊢
    exact hasSum_integral_iUnion (fun k => measurableSet_negShell hπ k) (negShell_disjoint hπ) hInt

  have hsplit : ∫ x in Oᶜ, g x ∂μ
      = (∑ k ∈ Finset.range m', ∫ x in negShell hπ k, g x ∂μ)
        + ∑' j : ℕ, ∫ x in negShell hπ (j + m'), g x ∂μ := by
    rw [← hHas.tsum_eq, hHas.summable.sum_add_tsum_nat_add m']
  have htail : ∑' j : ℕ, ∫ x in negShell hπ (j + m'), g x ∂μ
      = B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * (1 - a)⁻¹ := by
    have h2 : HasSum (fun j : ℕ => B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * a ^ j)
        (B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * (1 - a)⁻¹) :=
      (hasSum_geometric_of_norm_lt_one ha1).mul_left _
    have h : (fun j : ℕ => ∫ x in negShell hπ (j + m'), g x ∂μ)
        = fun j => B 0 * (∫ u in genShell hπ 0, charExt χ⁻¹ u ∂μ) * a ^ (m' + 1) * a ^ j := by
      funext j
      rw [htailval (j + m') (by omega), show j + m' + 1 = (m' + 1) + j by ring, pow_add]
      ring
    rw [h]
    exact h2.tsum_eq
  have hlow : ∑ k ∈ Finset.range m', ∫ x in negShell hπ k, g x ∂μ
      = ∑ n ∈ Finset.Ico 1 (m' + 1), (N ^ (-(2 * s + 1))) ^ n
          * ∫ x in {x : v.adicCompletion F | Valued.v x = (Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ)},
              charExt χ⁻¹ x * B x⁻¹ ∂μ := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hlowval k, add_comm k 1]

  have hOmeas : MeasurableSet O := (isCompact_integers (F := F) (v := v)).isClosed.measurableSet
  have hint1 : Integrable (O.indicator A) μ := hA.integrable_indicator hOmeas
  have hint2 : Integrable (Oᶜ.indicator g) μ := hInt.integrable_indicator hOmeas.compl
  have hunit : {u : v.adicCompletion F | Valued.v u = 1} = genShell hπ 0 := setOf_valued_eq_one_eq_genShell hπ
  rw [integral_add hint1 hint2, integral_indicator hOmeas, integral_indicator hOmeas.compl, hsplit, hlow, htail,
    hunit]
  ring

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end LocalIntertwining.SmoothShell
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end SmoothShell_Main
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x ∂μ)
        + (∑ n ∈ Finset.Ico 1 m,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ n
              * ∫ x in {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (n : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ ∂μ)
        + B 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1}, LanglandsTunnell.TateLocal.charExt χ⁻¹ u ∂μ)
            * (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ m
            * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
  LocalIntertwining.SmoothShell.integral_smoothWeylIntegrand_impl F v μ ϖ hϖ χ hχ m hm A hA B hB s hs

end S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion (solution)
