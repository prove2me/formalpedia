-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3f0bd471-1523-5e28-b4ca-8a9004133413

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion

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

private theorem ordA_unit (u : Aˣ) : ordA A (u : A) = 0 :=
  ordA_unique A u.ne_zero (by rw [span_singleton_eq_top.mpr u.isUnit, pow_zero, one_eq_top])

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

noncomputable def ord : Additive Lˣ →+ ℤ where
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

theorem ord_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) {na nb : ℕ}
    (hna : span {a} = maximalIdeal A ^ na) (hnb : span {b} = maximalIdeal A ^ nb) :
    ord A (.ofMul x) = (na : ℤ) - nb := by
  have := ordZ_spec A ha hb hx
  rw [ordA_unique A ha hna, ordA_unique A hb hnb] at this
  exact this

theorem ord_ofMul_of_mem {x : Lˣ} (hx : (x : L) ∈ A) {n : ℕ}
    (hspan : span {(⟨(x : L), hx⟩ : A)} = maximalIdeal A ^ n) :
    ord A (.ofMul x) = n := by
  have h := ord_spec A (coe_mk_ne_zero A x hx rfl) one_ne_zero
    (b := 1) (by push_cast; exact mul_one _) hspan
    (by rw [span_singleton_eq_top.mpr isUnit_one, pow_zero, one_eq_top])
  simpa using h

theorem ord_ofMul_mk0_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : A) : L) ≠ 0) :
    ord A (.ofMul (Units.mk0 ((ϖ : A) : L) h0)) = 1 := by
  refine ord_ofMul_of_mem A (x := Units.mk0 ((ϖ : A) : L) h0) (ϖ : A).2 ?_
  have hmk : (⟨((Units.mk0 ((ϖ : A) : L) h0 : Lˣ) : L), (ϖ : A).2⟩ : A) = ϖ :=
    Subtype.ext rfl
  rw [hmk, pow_one, ← hϖ.maximalIdeal_eq]

theorem ord_surjective : Function.Surjective (ord A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have h0 : ((ϖ : A) : L) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  intro k
  refine ⟨.ofMul ((Units.mk0 ((ϖ : A) : L) h0) ^ k), ?_⟩
  rw [show Additive.ofMul ((Units.mk0 ((ϖ : A) : L) h0) ^ k)
        = k • Additive.ofMul (Units.mk0 ((ϖ : A) : L) h0) from rfl,
    map_zsmul, ord_ofMul_mk0_of_irreducible A hϖ h0, smul_eq_mul, mul_one]

theorem ord_eq_zero_iff (x : Lˣ) :
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

omit [IsDiscreteValuationRing ↥A] in
private theorem map_maximalIdeal_ringEquiv (e : A ≃+* A) :
    Ideal.map (e : A →+* A) (maximalIdeal A) = maximalIdeal A := by
  have key : ∀ f : A ≃+* A, Ideal.map (f : A →+* A) (maximalIdeal A) ≤ maximalIdeal A := by
    intro f
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy
    intro hu
    exact hy (by simpa using hu.map f.symm.toRingHom)
  refine le_antisymm (key e) ?_
  intro y hy
  have : e.symm y ∈ maximalIdeal A := by
    have := key e.symm
    rw [Ideal.map_le_iff_le_comap] at this
    exact this hy
  simpa using mem_map_of_mem (e : A →+* A) this

private theorem ordA_ringEquiv (e : A ≃+* A) {a : A} (ha : a ≠ 0) :
    ordA A (e a) = ordA A a := by
  have hea : e a ≠ 0 := by
    intro h0
    exact ha (by simpa using congrArg e.symm h0)
  refine ordA_unique A hea ?_
  have : span {e a} = Ideal.map (e : A →+* A) (span {a}) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [this, ordA_span A ha, Ideal.map_pow, map_maximalIdeal_ringEquiv A e]

theorem ord_units_map_of_mem_decompositionSubgroup {K : Type*} [Field K] [Algebra K L]
    {d : L ≃ₐ[K] L} (hd : d ∈ A.decompositionSubgroup K) (x : Lˣ) :
    ord A (.ofMul (Units.map d.toAlgHom.toRingHom.toMonoidHom x)) = ord A (.ofMul x) := by
  obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x
  set e : A ≃+* A :=
    MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A (⟨d, hd⟩ : A.decompositionSubgroup K)
    with he
  have hcoe : ∀ c : A, ((e c : A) : L) = d (c : L) := fun c => rfl
  have hea : e a ≠ 0 := fun h0 => ha (by simpa using congrArg e.symm h0)
  have heb : e b ≠ 0 := fun h0 => hb (by simpa using congrArg e.symm h0)
  have hrep : ((Units.map d.toAlgHom.toRingHom.toMonoidHom x : Lˣ) : L) * ((e b : A) : L)
      = ((e a : A) : L) := by
    rw [hcoe, hcoe]
    have := congrArg d hx
    rw [map_mul] at this
    simpa using this
  have h1 := ordZ_spec A hea heb hrep
  have h2 := ordZ_spec A ha hb hx
  show ordZ A (Units.map d.toAlgHom.toRingHom.toMonoidHom x) = ordZ A x
  rw [h1, h2, ordA_ringEquiv A e ha, ordA_ringEquiv A e hb]

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

theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

theorem card_residueField_pos :
    0 < Nat.card (ResidueField (v.adicCompletionIntegers F)) :=
  Nat.card_pos

section CosetStep

variable {F v}

theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
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

theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in

theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
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

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in

theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
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

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in

theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
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

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in

theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
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

theorem distribHaarChar_eq_one_of_mem_range (x : (v.adicCompletion F)ˣ)
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

theorem distribHaarChar_mk0_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
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

theorem distribHaarChar_adicCompletion (x : (v.adicCompletion F)ˣ) :
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

theorem measure_smul_integers [MeasurableSpace (v.adicCompletion F)]
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

abbrev normQ (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)

theorem modulus_coe_units_adicCompletion (u : (v.adicCompletion F)ˣ) :
    modulus (u : v.adicCompletion F) = normQ v ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F)
      (Additive.ofMul u))) := by
  rw [modulus_coe_units]
  exact LocalHaarModulus.distribHaarChar_adicCompletion u

theorem modulus_of_ne_zero_adicCompletion {x : v.adicCompletion F} (hx : x ≠ 0) :
    modulus x = normQ v ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F)
      (Additive.ofMul (Units.mk0 x hx)))) := by
  rw [modulus_of_ne_zero hx]
  exact LocalHaarModulus.distribHaarChar_adicCompletion (Units.mk0 x hx)

section Shells

variable {ϖ : v.adicCompletionIntegers F}

theorem coe_ne_zero_of_irreducible (hϖ : Irreducible ϖ) :
    ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)

def piUnit (hϖ : Irreducible ϖ) : (v.adicCompletion F)ˣ := Units.mk0 _ (coe_ne_zero_of_irreducible hϖ)

@[scoped simp] theorem piUnit_val (hϖ : Irreducible ϖ) :
    ((piUnit hϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl

theorem ord_piUnit (hϖ : Irreducible ϖ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ)) = 1 :=
  ValuationOrd.ord_ofMul_mk0_of_irreducible _ hϖ _

theorem ord_piUnit_pow (hϖ : Irreducible ϖ) (k : ℕ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ((piUnit hϖ) ^ k)) = k := by
  have h : Additive.ofMul ((piUnit hϖ) ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_nsmul, ord_piUnit]
  simp

def shellSet (hϖ : Irreducible ϖ) (k : ℕ) : Set (v.adicCompletion F) :=
  (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    \ (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

theorem isCompact_integers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  NumberField.isCompactAdicCompletionIntegers F v

theorem isCompact_smul_integers (c : v.adicCompletion F) :
    IsCompact (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have h := (isCompact_integers (F := F) (v := v)).image (continuous_const_smul c)
  rwa [Set.image_smul] at h

theorem measurableSet_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (c : v.adicCompletion F) :
    MeasurableSet (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  (isCompact_smul_integers c).isClosed.measurableSet

theorem measurableSet_shellSet [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (hϖ : Irreducible ϖ) (k : ℕ) :
    MeasurableSet (shellSet hϖ k) :=
  (measurableSet_smul_integers _).diff (measurableSet_smul_integers _)

theorem mem_smul_integers_iff {c x : v.adicCompletion F} :
    x ∈ c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ↔ ∃ y : v.adicCompletionIntegers F, c * (y : v.adicCompletion F) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, (smul_eq_mul c y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y : v.adicCompletion F), y.2, by show c • (y : v.adicCompletion F) = x; rw [smul_eq_mul]; exact hy⟩

theorem smul_integers_succ_subset (hϖ : Irreducible ϖ) (k : ℕ) :
    (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      ⊆ (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hx
  refine mem_smul_integers_iff.mpr ⟨ϖ * y, ?_⟩
  rw [← hy]
  push_cast [pow_succ, piUnit_val]
  ring

theorem shellSet_subset_integers (hϖ : Irreducible ϖ) (k : ℕ) :
    shellSet hϖ k ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hx.1
  rw [← hy]
  push_cast [piUnit_val]
  exact mul_mem (pow_mem ϖ.2 k) y.2

theorem zero_notMem_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : (0 : v.adicCompletion F) ∉ shellSet hϖ k := by
  intro h
  exact h.2 (mem_smul_integers_iff.mpr ⟨0, by push_cast; ring⟩)

theorem mem_shellSet_iff_ord_eq (hϖ : Irreducible ϖ) (k : ℕ) {x : v.adicCompletion F} (hx : x ≠ 0) :
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

theorem shellSet_subset_compl_zero (hϖ : Irreducible ϖ) (k : ℕ) :
    shellSet hϖ k ⊆ ({0}ᶜ : Set (v.adicCompletion F)) :=
  fun _ hx hx0 => zero_notMem_shellSet hϖ k ((Set.mem_singleton_iff.mp hx0) ▸ hx)

theorem shellSet_disjoint (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint (shellSet hϖ)) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun x hx hx' => hkk' ?_
  have hx0 : x ≠ 0 := fun h => zero_notMem_shellSet hϖ k (h ▸ hx)
  have h1 := (mem_shellSet_iff_ord_eq hϖ k hx0).mp hx
  have h2 := (mem_shellSet_iff_ord_eq hϖ k' hx0).mp hx'
  have h12 := h1.symm.trans h2
  exact_mod_cast h12

set_option synthInstance.maxHeartbeats 320000 in

theorem integers_diff_zero_eq_iUnion (hϖ : Irreducible ϖ) :
    ((v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ {0}) = ⋃ k : ℕ, shellSet hϖ k := by
  ext x
  constructor
  · rintro ⟨hxO, hx0⟩
    have hx : x ≠ 0 := hx0
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (x := (⟨x, hxO⟩ : v.adicCompletionIntegers F)) (fun h => hx (by
        simpa using congrArg (Subtype.val) h)) hϖ
    have hspan : Ideal.span {(⟨x, hxO⟩ : v.adicCompletionIntegers F)}
        = maximalIdeal (v.adicCompletionIntegers F) ^ n := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.span_singleton_eq_span_singleton.mpr hn.symm]
    have hord := ValuationOrd.ord_ofMul_of_mem (v.adicCompletionIntegers F)
      (x := Units.mk0 x hx) hxO hspan
    exact mem_iUnion.mpr ⟨n, (mem_shellSet_iff_ord_eq hϖ n hx).mpr hord⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨shellSet_subset_integers hϖ k hk,
      fun h => zero_notMem_shellSet hϖ k (h ▸ hk)⟩

end Shells

theorem one_le_normQ : (1 : ℝ≥0) ≤ normQ v := by
  have hpos := LocalHaarModulus.card_residueField_pos (F := F) (v := v)
  have hcard := LocalHaarModulus.card_residueField_eq_absNorm (F := F) (v := v)
  have h1 : 1 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h1

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable {ϖ : v.adicCompletionIntegers F}
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace (v.adicCompletion F)] [μ.Regular] in
theorem measure_integers_lt_top : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ :=
  (isCompact_integers (F := F) (v := v)).measure_lt_top

theorem measure_smul_integers_pow (hϖ : Irreducible ϖ) (k : ℕ) :
    μ (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (normQ v ^ (-(k : ℤ)) : ℝ≥0) * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have h := LocalHaarModulus.measure_smul_integers μ (piUnit hϖ ^ k)
  rwa [ord_piUnit_pow] at h

theorem measure_shellSet (hϖ : Irreducible ϖ) (k : ℕ) :
    μ (shellSet hϖ k)
      = ((normQ v ^ (-(k : ℤ)) * (1 - (normQ v)⁻¹) : ℝ≥0) : ℝ≥0∞)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hsub := smul_integers_succ_subset hϖ k
  have hfin : μ (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ≠ ∞ := by
    rw [measure_smul_integers_pow μ hϖ]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_integers_lt_top μ).ne
  rw [shellSet, measure_diff hsub ((measurableSet_smul_integers _).nullMeasurableSet) hfin,
    measure_smul_integers_pow μ hϖ, measure_smul_integers_pow μ hϖ]
  rw [← ENNReal.sub_mul (fun _ _ => (measure_integers_lt_top μ).ne)]
  congr 1
  rw [← ENNReal.coe_sub]
  congr 1
  rw [mul_tsub, mul_one]
  congr 1
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, mul_inv]

end Measures

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

theorem modulus_of_mem_shellSet (hϖ : Irreducible ϖ) {k : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ shellSet hϖ k) :
    modulus x = (normQ v ^ (-(k : ℤ)) : ℝ≥0) := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_shellSet hϖ k (h ▸ hx)
  rw [modulus_of_ne_zero_adicCompletion hx0,
    (mem_shellSet_iff_ord_eq hϖ k hx0).mp hx]

theorem charExt_of_mem_shellSet (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    {k : ℕ} {x : v.adicCompletion F} (hx : x ∈ shellSet hϖ k) :
    charExt χ x = (charExt χ ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)) ^ k := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_shellSet hϖ k (h ▸ hx)
  have hord := (mem_shellSet_iff_ord_eq hϖ k hx0).mp hx
  set w : (v.adicCompletion F)ˣ := Units.mk0 x hx0 * (piUnit hϖ ^ k)⁻¹ with hwdef
  have hword : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
    have hsub : Additive.ofMul w = Additive.ofMul (Units.mk0 x hx0)
        - Additive.ofMul (piUnit hϖ ^ k) := rfl
    rw [hsub, map_sub, hord, ord_piUnit_pow, sub_self]
  have hχw : χ w = 1 := hχ w ((ValuationOrd.ord_eq_zero_iff _ _).mp hword)
  have hfac : Units.mk0 x hx0 = piUnit hϖ ^ k * w := by
    rw [hwdef, mul_comm (Units.mk0 x hx0) ((piUnit hϖ ^ k)⁻¹), mul_inv_cancel_left]
  rw [charExt_of_ne_zero χ hx0, hfac, map_mul, hχw, mul_one, map_pow]
  have hϖ0 := coe_ne_zero_of_irreducible hϖ
  rw [charExt_of_ne_zero χ hϖ0]
  norm_cast

theorem ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ) :
    (((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg ha n) ha, ih,
        pow_succ]

theorem cpow_qpow_bridge (s : ℂ) (k : ℕ) :
    ((((normQ v) ^ (-(k : ℤ)) : ℝ≥0) : ℝ) : ℂ) ^ s
      = ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-s)) ^ k := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hq0 : (0 : ℝ) < ((normQ v : ℝ≥0) : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos hq1
  have hinv : ((((normQ v) ^ (-(k : ℤ)) : ℝ≥0) : ℝ)) = (((normQ v : ℝ≥0) : ℝ))⁻¹ ^ k := by
    push_cast
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [show ((((normQ v) ^ (-(k : ℤ)) : ℝ≥0) : ℝ) : ℂ)
        = (((((normQ v : ℝ≥0) : ℝ))⁻¹ ^ k : ℝ) : ℂ) by exact_mod_cast congrArg Complex.ofReal hinv]
  rw [ofReal_pow_cpow (inv_nonneg.mpr hq0.le) s k]
  congr 1
  push_cast
  rw [Complex.inv_cpow _ _
      (by rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero),
    ← Complex.cpow_neg]

end Integrand

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable {ϖ : v.adicCompletionIntegers F}
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

def eulerVar (ϖ : v.adicCompletionIntegers F) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  charExt χ ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
    * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-s)

omit [μ.IsAddHaarMeasure] [μ.Regular] in

theorem mulMeasure_restrict_shellSet (hϖ : Irreducible ϖ) (k : ℕ) :
    (mulMeasure μ).restrict (shellSet hϖ k)
      = ((normQ v ^ (k : ℤ) : ℝ≥0) : ℝ≥0∞) • μ.restrict (shellSet hϖ k) := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hqne : (normQ v : ℝ≥0) ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  have hS := measurableSet_shellSet (F := F) (v := v) hϖ k
  rw [mulMeasure, restrict_withDensity hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr (shellSet_subset_compl_zero hϖ k)]
  rw [withDensity_congr_ae (f := fun x => ((modulus x : ℝ≥0∞))⁻¹)
    (g := fun _ => ((normQ v ^ (k : ℤ) : ℝ≥0) : ℝ≥0∞))
    (by
      rw [Filter.EventuallyEq, ae_restrict_iff' hS]
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [modulus_of_mem_shellSet hϖ hx, ← ENNReal.coe_inv (by positivity), ← zpow_neg,
        neg_neg])]
  rw [withDensity_const]

theorem setIntegral_shellSet_const (hϖ : Irreducible ϖ) (k : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : v.adicCompletion F → E) (c : E)
    (hA : Set.EqOn A (fun _ => c) (shellSet hϖ k)) :
    ∫ x in shellSet hϖ k, A x ∂(mulMeasure μ)
      = ((((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ) * μ.real (v.adicCompletionIntegers F :
          Set (v.adicCompletion F)))) • c := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hqne : (normQ v : ℝ≥0) ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  have hS := measurableSet_shellSet (F := F) (v := v) hϖ k
  rw [show (∫ x in shellSet hϖ k, A x ∂(mulMeasure μ))
        = ∫ x, A x ∂((mulMeasure μ).restrict (shellSet hϖ k)) from rfl,
    mulMeasure_restrict_shellSet μ hϖ k, integral_smul_measure]
  rw [show (∫ x, A x ∂(μ.restrict (shellSet hϖ k)))
        = ∫ x in shellSet hϖ k, A x ∂μ from rfl,
    setIntegral_congr_fun hS hA, setIntegral_const, smul_smul]
  congr 1
  have hsh : μ.real (shellSet hϖ k)
      = (((normQ v ^ (-(k : ℤ)) * (1 - (normQ v)⁻¹) : ℝ≥0)) : ℝ)
        * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show (μ (shellSet hϖ k)).toReal = _
    rw [measure_shellSet μ hϖ k, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rfl
  rw [hsh, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_zpow, NNReal.coe_zpow]
  rw [show ((normQ v : ℝ≥0) : ℝ) ^ (k : ℤ)
        * (((normQ v : ℝ≥0) : ℝ) ^ (-(k : ℤ)) * (((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ)
          * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (((normQ v : ℝ≥0) : ℝ) ^ (k : ℤ) * ((normQ v : ℝ≥0) : ℝ) ^ (-(k : ℤ)))
        * ((((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ)
          * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) from by ring]
  rw [← zpow_add₀ (by positivity : ((normQ v : ℝ≥0) : ℝ) ≠ 0)]
  simp

omit [μ.Regular] in

theorem mulMeasure_shellSet_lt_top (hϖ : Irreducible ϖ) (k : ℕ) :
    mulMeasure μ (shellSet hϖ k) < ∞ := by
  have hS := measurableSet_shellSet (F := F) (v := v) hϖ k
  have h1 : mulMeasure μ (shellSet hϖ k)
      = ((mulMeasure μ).restrict (shellSet hϖ k)) (shellSet hϖ k) := by
    rw [Measure.restrict_apply hS, Set.inter_self]
  rw [h1, mulMeasure_restrict_shellSet μ hϖ k, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hS, Set.inter_self]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_of_le_of_lt (measure_mono (shellSet_subset_integers hϖ k)) (measure_integers_lt_top μ))

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in

theorem indicator_integrand (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : v.adicCompletion F) :
    (Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        (fun _ => (1 : ℂ)) x) * charExt χ x * (((modulus x : ℝ)) : ℂ) ^ s
      = Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          (fun y => charExt χ y * (((modulus y : ℝ)) : ℂ) ^ s) x := by
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul]

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in

theorem eqOn_integrand_shellSet (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    (s : ℂ) (k : ℕ) :
    Set.EqOn (fun y => charExt χ y * (((modulus y : ℝ)) : ℂ) ^ s)
      (fun _ => eulerVar ϖ χ s ^ k) (shellSet hϖ k) := by
  intro x hx
  have h1 := charExt_of_mem_shellSet hϖ hχ hx
  have h2 := modulus_of_mem_shellSet hϖ hx
  simp only
  rw [h1, h2, cpow_qpow_bridge s k, eulerVar, mul_pow]

theorem hasSum_localZeta_indicator (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    (s : ℂ) (hconv : ‖eulerVar ϖ χ s‖ < 1) :
    HasSum (fun k : ℕ => eulerVar ϖ χ s ^ k
        * (((((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ)
            * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ)) : ℂ))
      (localZeta μ (Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        (fun _ => (1 : ℂ))) χ s) := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  set g : v.adicCompletion F → ℂ :=
    fun y => charExt χ y * (((modulus y : ℝ)) : ℂ) ^ s with hg
  set C : ℝ := (((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ))
    * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hC
  have hOmeas : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (isCompact_integers (F := F) (v := v)).isClosed.measurableSet

  have hze : mulMeasure μ ({0} : Set (v.adicCompletion F)) = 0 := by
    rw [mulMeasure, withDensity_apply _ (measurableSet_singleton (0 : v.adicCompletion F)),
      Measure.restrict_restrict (measurableSet_singleton (0 : v.adicCompletion F)),
      Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]
  have hae : (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      =ᵐ[mulMeasure μ]
        (((v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ {0} :
          Set (v.adicCompletion F))) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (fun x hx => ?_) hze
      by_contra hx0
      exact hx.2 ⟨hx.1, hx0⟩
    · have h0 : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ {0})
          \ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = ∅ :=
        Set.diff_eq_empty.mpr Set.diff_subset
      rw [h0]
      exact measure_empty
  have hloc : localZeta μ (Set.indicator
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (fun _ => (1 : ℂ))) χ s
      = ∫ x in (⋃ k : ℕ, shellSet hϖ k), g x ∂(mulMeasure μ) := by
    rw [localZeta]
    rw [show (∫ x, Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          (fun _ => (1 : ℂ)) x * charExt χ x * (((modulus x : ℝ)) : ℂ) ^ s ∂(mulMeasure μ))
        = ∫ x, Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F)) g x
            ∂(mulMeasure μ) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => indicator_integrand χ s x)]
    rw [MeasureTheory.integral_indicator hOmeas,
      show ((mulMeasure μ).restrict (v.adicCompletionIntegers F :
          Set (v.adicCompletion F)))
        = ((mulMeasure μ).restrict ((v.adicCompletionIntegers F :
          Set (v.adicCompletion F)) \ {0})) from Measure.restrict_congr_set hae,
      integers_diff_zero_eq_iUnion hϖ]

  have hiOn : ∀ k : ℕ, IntegrableOn g (shellSet hϖ k) (mulMeasure μ) := by
    intro k
    refine (integrableOn_congr_fun (eqOn_integrand_shellSet hϖ hχ s k)
      (measurableSet_shellSet hϖ k)).mpr ?_
    exact integrableOn_const ((mulMeasure_shellSet_lt_top μ hϖ k).ne)
  have hnorm : ∀ k : ℕ,
      (∫ x in shellSet hϖ k, ‖g x‖ ∂(mulMeasure μ)) = ‖eulerVar ϖ χ s‖ ^ k * C := by
    intro k
    have heq : Set.EqOn (fun y => ‖g y‖) (fun _ => ‖eulerVar ϖ χ s ^ k‖)
        (shellSet hϖ k) := fun x hx => by
      have h' : charExt χ x * (((modulus x : ℝ)) : ℂ) ^ s = eulerVar ϖ χ s ^ k :=
        eqOn_integrand_shellSet hϖ hχ s k hx
      simp only [hg]
      rw [h']
    rw [setIntegral_shellSet_const μ hϖ k _ _ heq, smul_eq_mul, norm_pow, mul_comm]
  have hsummable : Summable fun k : ℕ => ∫ x in shellSet hϖ k, ‖g x‖ ∂(mulMeasure μ) := by
    rw [show (fun k : ℕ => ∫ x in shellSet hϖ k, ‖g x‖ ∂(mulMeasure μ))
        = fun k : ℕ => ‖eulerVar ϖ χ s‖ ^ k * C from funext hnorm]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hconv).mul_right C
  have hInt : IntegrableOn g (⋃ k : ℕ, shellSet hϖ k) (mulMeasure μ) :=
    MeasureTheory.integrableOn_iUnion_of_summable_integral_norm hiOn hsummable
  have hshellval : ∀ k : ℕ,
      (∫ x in shellSet hϖ k, g x ∂(mulMeasure μ)) = eulerVar ϖ χ s ^ k * (C : ℂ) := by
    intro k
    rw [setIntegral_shellSet_const μ hϖ k _ _ (eqOn_integrand_shellSet hϖ hχ s k)]
    rw [Complex.real_smul, mul_comm]
  have hsum := MeasureTheory.hasSum_integral_iUnion
    (fun k => measurableSet_shellSet hϖ k)
    (shellSet_disjoint hϖ) hInt
  rw [show (fun k : ℕ => ∫ x in shellSet hϖ k, g x ∂(mulMeasure μ))
      = fun k : ℕ => eulerVar ϖ χ s ^ k * (C : ℂ) from funext hshellval] at hsum
  rw [hloc]
  exact hsum

theorem localZeta_indicator_integers (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    (s : ℂ) (hconv : ‖eulerVar ϖ χ s‖ < 1) :
    localZeta μ (Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        (fun _ => (1 : ℂ))) χ s
      = ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ)
        * (1 - ((((normQ v : ℝ≥0) : ℝ)) : ℂ)⁻¹) * (1 - eulerVar ϖ χ s)⁻¹ := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have h := (hasSum_localZeta_indicator μ hϖ hχ s hconv).tsum_eq
  rw [← h, tsum_mul_right, tsum_geometric_of_norm_lt_one hconv]
  have hqR : (1 : ℝ) ≤ ((normQ v : ℝ≥0) : ℝ) := by exact_mod_cast hq1
  have hsub : (((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ))
      = 1 - (((normQ v : ℝ≥0) : ℝ))⁻¹ := by
    rw [NNReal.coe_sub (by
      rw [inv_le_one_iff₀]
      right
      exact hq1)]
    push_cast
    ring
  rw [hsub]
  push_cast
  ring

end Zeta

end LocalZetaUnramified
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_LocalZetaUnramified
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

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

theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have hr : Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F)
      = {(0 : v.adicCompletion F)}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [hr]
  exact isClosed_singleton.isOpen_compl

theorem image_val_subset_compl_zero (A : Set (v.adicCompletion F)ˣ) :
    (Units.val '' A) ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

theorem smul_set_eq_preimage {c : v.adicCompletion F} (hc : c ≠ 0)
    (S : Set (v.adicCompletion F)) :
    c • S = (fun y => c⁻¹ * y) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

theorem isOpen_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : IsOpen S) :
    IsOpen (c • S) := by
  have h : c • S = (Homeomorph.mulLeft₀ c hc) '' S := by
    ext x
    simp [Homeomorph.coe_mulLeft₀, Set.mem_smul_set, smul_eq_mul, Set.mem_image]
  rw [h]
  exact (Homeomorph.mulLeft₀ c hc).isOpenMap _ hS

theorem image_val_smul (g : (v.adicCompletion F)ˣ) (A : Set (v.adicCompletion F)ˣ) :
    Units.val '' (g • A) = (g : v.adicCompletion F) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : v.adicCompletion F), ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g * a, ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩

variable {ϖ : v.adicCompletionIntegers F}

theorem isOpen_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : IsOpen (shellSet hϖ k) := by
  unfold shellSet
  refine IsOpen.sdiff (isOpen_smul_set (Units.ne_zero _) ?_) ?_
  · exact Valued.isOpen_valuationSubring _
  · rw [smul_set_eq_preimage (Units.ne_zero _)]
    exact (Valued.isClosed_valuationSubring _).preimage (continuous_const_mul _)

theorem one_mem_shellSet_zero (hϖ : Irreducible ϖ) :
    (1 : v.adicCompletion F) ∈ shellSet hϖ 0 := by
  have h10 : (1 : v.adicCompletion F) ≠ 0 := one_ne_zero
  rw [mem_shellSet_iff_ord_eq hϖ 0 h10]
  have h1 : Units.mk0 (1 : v.adicCompletion F) h10 = 1 := Units.ext (by simp)
  rw [h1]
  simp

theorem ord_ofMul_mul (u w : (v.adicCompletion F)ˣ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (u * w))
      = ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u)
        + ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) := by
  have h : Additive.ofMul (u * w) = Additive.ofMul u + Additive.ofMul w := rfl
  rw [h, map_add]

theorem ord_ofMul_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ ^ k)) = k := by
  have h : Additive.ofMul (piUnit hϖ ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_zsmul, ord_piUnit hϖ, smul_eq_mul, mul_one]

def genShell (hϖ : Irreducible ϖ) (k : ℤ) : Set (v.adicCompletion F) :=
  ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0

theorem mem_genShell_iff (hϖ : Irreducible ϖ) {k : ℤ} {x : v.adicCompletion F} (hx : x ≠ 0) :
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

theorem genShell_disjoint (hϖ : Irreducible ϖ) :
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

theorem iUnion_genShell (hϖ : Irreducible ϖ) :
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

theorem measurableSet_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : MeasurableSet S) :
    MeasurableSet (c • S) := by
  rw [smul_set_eq_preimage hc]
  exact hS.preimage (measurable_const_mul _)

theorem measurableSet_genShell (hϖ : Irreducible ϖ) (k : ℤ) :
    MeasurableSet (genShell hϖ k) :=
  measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0)

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace (v.adicCompletion F)] [μ.IsAddHaarMeasure] [μ.Regular] in

theorem mulMeasure_eq_of_subset_smul_shell (hϖ : Irreducible ϖ)
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

theorem measure_units_smul (u : (v.adicCompletion F)ˣ) (S : Set (v.adicCompletion F)) :
    μ ((u : v.adicCompletion F) • S)
      = (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ S := by
  rw [distribHaarChar_mul]
  rfl

theorem mulMeasure_units_smul (hϖ : Irreducible ϖ) (u : (v.adicCompletion F)ˣ)
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

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
  isOpenEmbedding_val.measurableEmbedding

def mulHaar : Measure (v.adicCompletion F)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulHaar_apply {A : Set (v.adicCompletion F)ˣ} (hA : MeasurableSet A) :
    mulHaar μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => measurableEmbedding_val.measurableSet_image' hs) _ hA

theorem isMulLeftInvariant_mulHaar (hϖ : Irreducible ϖ) :
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

theorem isFiniteMeasureOnCompacts_mulHaar (hϖ : Irreducible ϖ) :
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

theorem isOpenPosMeasure_mulHaar (hϖ : Irreducible ϖ) :
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

theorem isHaarMeasure_mulHaar (hϖ : Irreducible ϖ) : (mulHaar μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaar μ hϖ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaar μ hϖ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaar μ hϖ }

end MulHaarFromAdditive
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_MulHaarFromAdditive
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

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

theorem valued_ne_zero_of_ne_zero {x : v.adicCompletion F} (hx : x ≠ 0) :
    Valued.v x ≠ 0 := by
  intro h0
  have h1 : Valued.v x * Valued.v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem valued_coe_ne_zero (x : (v.adicCompletion F)ˣ) :
    Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 :=
  valued_ne_zero_of_ne_zero x.ne_zero

theorem valued_le_one_of_mem {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v x ≤ 1 :=
  hx

theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Integers (v.adicCompletionIntegers F) :=
  Valuation.valuationSubring.integers _

theorem exists_irreducible_valued :
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

theorem valued_coe_of_irreducible (hϖ : Irreducible ϖ) :
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

theorem valued_coe_units_eq_exp_neg_ord (x : (v.adicCompletion F)ˣ) :
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

theorem coe_mem_integers_iff_ord_nonneg (x : (v.adicCompletion F)ˣ) :
    ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      ↔ 0 ≤ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) := by
  rw [mem_adicCompletionIntegers, valued_coe_units_eq_exp_neg_ord, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

theorem valued_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    Valued.v (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
      = WithZero.exp (-k) := by
  rw [valued_coe_units_eq_exp_neg_ord, ord_ofMul_zpow_piUnit hϖ]

end ValuedOrdBridge
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_ValuedOrdBridge
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

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

theorem valued_eq_one_of_ord_eq_zero (u : (v.adicCompletion F)ˣ)
    (hu : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0) :
    Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
  rw [valued_coe_units_eq_exp_neg_ord, hu, neg_zero, WithZero.exp_zero]

theorem ord_eq_one_of_valued (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v ((ϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ) = 1 := by
  have h := valued_coe_units_eq_exp_neg_ord ϖ
  rw [hϖ] at h
  have h' : WithZero.exp (-1 : ℤ)
      = WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ))) := h
  have h'' := WithZero.exp_injective h'
  omega

variable {χ : (v.adicCompletion F)ˣ →* ℂˣ}

theorem char_eq_one_of_ord_eq_zero
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (u : (v.adicCompletion F)ˣ)
    (hu : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0) : χ u = 1 :=
  hχ u (valued_eq_one_of_ord_eq_zero u hu)

variable {π : v.adicCompletionIntegers F}

theorem char_eq_zpow_of_ord (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (x : (v.adicCompletion F)ˣ) (k : ℤ)
    (hk : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) = k) :
    χ x = χ (piUnit hπ) ^ k := by
  have hu : ValuationOrd.ord (v.adicCompletionIntegers F)
      (Additive.ofMul ((piUnit hπ ^ k)⁻¹ * x)) = 0 := by
    rw [ord_ofMul_mul, show ((piUnit hπ ^ k)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hπ ^ (-k) from
      (zpow_neg _ _).symm, ord_ofMul_zpow_piUnit hπ, hk]
    ring
  have hx : x = piUnit hπ ^ k * ((piUnit hπ ^ k)⁻¹ * x) := by rw [mul_inv_cancel_left]
  calc χ x = χ (piUnit hπ ^ k * ((piUnit hπ ^ k)⁻¹ * x)) := by rw [← hx]
    _ = χ (piUnit hπ) ^ k * 1 := by rw [map_mul, map_zpow, char_eq_one_of_ord_eq_zero hχ _ hu]
    _ = χ (piUnit hπ) ^ k := mul_one _

theorem char_eq_char_piUnit (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v ((ϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    χ ϖ = χ (piUnit hπ) := by
  rw [char_eq_zpow_of_ord hπ hχ ϖ 1 (ord_eq_one_of_valued ϖ hϖ), zpow_one]

def negShell (hπ : Irreducible π) (m : ℕ) : Set (v.adicCompletion F) :=
  genShell hπ (-((m : ℤ) + 1))

theorem ne_zero_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) : x ≠ 0 := by
  have h : x ∈ ⋃ k : ℤ, genShell hπ k := Set.mem_iUnion.mpr ⟨_, hx⟩
  rw [iUnion_genShell hπ] at h
  exact h

theorem ord_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) (hx0 : x ≠ 0) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx0)) = -((m : ℤ) + 1) :=
  (mem_genShell_iff hπ hx0).mp hx

theorem compl_integers_eq_iUnion_negShell (hπ : Irreducible π) :
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

theorem negShell_disjoint (hπ : Irreducible π) :
    Pairwise (Function.onFun Disjoint (negShell hπ)) := by
  intro m m' hmm'
  have h : (-((m : ℤ) + 1)) ≠ (-((m' : ℤ) + 1)) := by
    intro h
    apply hmm'
    omega
  exact genShell_disjoint hπ h

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

theorem measurableSet_negShell (hπ : Irreducible π) (m : ℕ) : MeasurableSet (negShell hπ m) :=
  measurableSet_genShell hπ _

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in

theorem modulus_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) : modulus x = normQ v ^ (m + 1) := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_negShell hπ hx
  rw [modulus_of_ne_zero_adicCompletion hx0, ord_of_mem_negShell hπ hx hx0, neg_neg,
    show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in

theorem charExt_inv_of_mem_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    {m : ℕ} {x : v.adicCompletion F} (hx : x ∈ negShell hπ m) :
    charExt χ⁻¹ x = ((χ (piUnit hπ) : ℂˣ) : ℂ) ^ (m + 1) := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_negShell hπ hx
  rw [charExt_of_ne_zero χ⁻¹ hx0, MonoidHom.inv_apply,
    char_eq_zpow_of_ord hπ hχ (Units.mk0 x hx0) _ (ord_of_mem_negShell hπ hx hx0),
    ← zpow_neg, neg_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    Units.val_pow_eq_pow_val]

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in

theorem integrand_eqOn_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    Set.EqOn (fun y => charExt χ⁻¹ y * (((modulus y : ℝ)) : ℂ) ^ w)
      (fun _ => (((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w) ^ (m + 1))
      (negShell hπ m) := by
  intro x hx
  have hq0 : (0 : ℝ) ≤ ((normQ v : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  simp only
  rw [charExt_inv_of_mem_negShell hπ hχ hx, modulus_of_mem_negShell hπ hx, NNReal.coe_pow,
    ofReal_pow_cpow hq0 w (m + 1), mul_pow]

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

theorem measure_negShell (hπ : Irreducible π) (m : ℕ) :
    μ (negShell hπ m)
      = ((normQ v ^ (m + 1) * (1 - (normQ v)⁻¹) : ℝ≥0) : ℝ≥0∞)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hΔ : distribHaarChar (v.adicCompletion F) (piUnit hπ ^ (-((m : ℤ) + 1)))
      = normQ v ^ (m + 1) := by
    rw [LocalHaarModulus.distribHaarChar_adicCompletion, ord_ofMul_zpow_piUnit hπ, neg_neg,
      show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h0 := measure_shellSet μ hπ 0
  rw [show (-((0 : ℕ) : ℤ)) = 0 from by simp, zpow_zero, one_mul] at h0
  rw [negShell, genShell, measure_units_smul μ (piUnit hπ ^ (-((m : ℤ) + 1))) (shellSet hπ 0), hΔ, h0,
    ← mul_assoc, ← ENNReal.coe_mul]

omit [BorelSpace (v.adicCompletion F)] [μ.Regular] in
theorem measure_integers_lt_top' : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ :=
  (isCompact_integers (F := F) (v := v)).measure_lt_top

theorem measure_negShell_lt_top (hπ : Irreducible π) (m : ℕ) : μ (negShell hπ m) < ∞ := by
  rw [measure_negShell μ hπ m]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_integers_lt_top' μ)

theorem measureReal_negShell (hπ : Irreducible π) (m : ℕ) :
    μ.real (negShell hπ m)
      = ((normQ v : ℝ≥0) : ℝ) ^ (m + 1) * (((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ)
        * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [measureReal_def, measure_negShell μ hπ m, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_mul,
    NNReal.coe_pow, measureReal_def]

omit [μ.IsAddHaarMeasure] [μ.Regular] in

theorem setIntegral_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    ∫ x in negShell hπ m, charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w ∂μ
      = ((μ.real (negShell hπ m) : ℝ) : ℂ)
        * (((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w) ^ (m + 1) := by
  rw [setIntegral_congr_fun (measurableSet_negShell hπ m) (integrand_eqOn_negShell hπ hχ w m),
    setIntegral_const, Complex.real_smul]

omit [μ.IsAddHaarMeasure] [μ.Regular] in

theorem setIntegral_norm_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    ∫ x in negShell hπ m, ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w‖ ∂μ
      = μ.real (negShell hπ m)
        * ‖((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w‖ ^ (m + 1) := by
  have heq : Set.EqOn (fun x => ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w‖)
      (fun _ => ‖((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w‖ ^ (m + 1))
      (negShell hπ m) := by
    intro x hx
    have h := integrand_eqOn_negShell hπ hχ w m hx
    simp only at h ⊢
    rw [h, norm_pow]
  rw [setIntegral_congr_fun (measurableSet_negShell hπ m) heq, setIntegral_const, smul_eq_mul]

theorem integrableOn_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    IntegrableOn (fun x => charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w) (negShell hπ m) μ := by
  refine (integrableOn_congr_fun (integrand_eqOn_negShell hπ hχ w m) (measurableSet_negShell hπ m)).mpr ?_
  exact integrableOn_const ((measure_negShell_lt_top μ hπ m).ne)

end WeylGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_WeylGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

section FinGKFold_Main

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aP2DGK
namespace FinGK
namespace WeylGK

open LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge

theorem integral_unramifiedWeylIntegrand_impl
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
  haveI : μ.Regular := inferInstance

  obtain ⟨π, hπ, -⟩ := exists_irreducible_valued (v := v)

  set O : Set (v.adicCompletion F) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  set A : ℂ := ((χ ϖ : ℂˣ) : ℂ) with hA
  set N : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) with hN
  set t : ℂ := A * N ^ (-(2 * s)) with ht
  set g : v.adicCompletion F → ℂ :=
    fun y => charExt χ⁻¹ y * (((modulus y : ℝ)) : ℂ) ^ (-(2 * s + 1)) with hg
  set μO : ℝ := μ.real O with hμO

  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hQN : ((((normQ v : ℝ≥0) : ℝ) : ℂ)) = N := by
    rw [hN, normQ]
    push_cast
    rfl
  have hNR : (1 : ℝ) ≤ ((normQ v : ℝ≥0) : ℝ) := by exact_mod_cast hq1
  have hN0 : N ≠ 0 := by
    rw [← hQN]
    exact_mod_cast (lt_of_lt_of_le one_pos hNR).ne'
  have hAP : ((χ (piUnit hπ) : ℂˣ) : ℂ) = A := by
    rw [hA, char_eq_char_piUnit hπ hχ ϖ hϖ]

  have hpow : N ^ (-(2 * s + 1)) = N ^ (-(2 * s)) * N⁻¹ := by
    rw [show (-(2 * s + 1) : ℂ) = -(2 * s) + (-1) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one]
  have hr : ((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-(2 * s + 1)) = t * N⁻¹ := by
    rw [hAP, hQN, hpow, ht, mul_assoc]
  have hc0 : (((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ) = 1 - (((normQ v : ℝ≥0) : ℝ))⁻¹ := by
    rw [NNReal.coe_sub (inv_le_one_of_one_le₀ hq1)]
    push_cast
    ring

  have hterm : ∀ m : ℕ, ∫ x in negShell hπ m, g x ∂μ
      = (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * t ^ m) := by
    intro m
    rw [hg, setIntegral_negShell μ hπ hχ (-(2 * s + 1)) m, hr, measureReal_negShell μ hπ m, hc0, ← hμO]
    have hNt : (((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (m + 1) * (t * N⁻¹) ^ (m + 1) = t ^ (m + 1) := by
      rw [← mul_pow, hQN, mul_comm t N⁻¹, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
    push_cast
    calc (((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (m + 1) * (1 - ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) * (μO : ℂ)
          * (t * N⁻¹) ^ (m + 1)
        = (1 - ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) * (μO : ℂ)
          * ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (m + 1) * (t * N⁻¹) ^ (m + 1)) := by ring
      _ = (1 - ((((normQ v : ℝ≥0) : ℝ) : ℂ))⁻¹) * (μO : ℂ) * (t * t ^ m) := by rw [hNt, pow_succ']
  have hnorm : ∀ m : ℕ, ∫ x in negShell hπ m, ‖g x‖ ∂μ
      = ((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t‖) * ‖t‖ ^ m := by
    intro m
    rw [hg, setIntegral_norm_negShell μ hπ hχ (-(2 * s + 1)) m, hr, measureReal_negShell μ hπ m, hc0, ← hμO]
    have hNn : ‖(N : ℂ)⁻¹‖ = (((normQ v : ℝ≥0) : ℝ))⁻¹ := by
      rw [norm_inv, ← hQN, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    have hNt : (((normQ v : ℝ≥0) : ℝ)) ^ (m + 1) * ‖t * N⁻¹‖ ^ (m + 1) = ‖t‖ ^ (m + 1) := by
      rw [← mul_pow, norm_mul, hNn, mul_comm ‖t‖ _, ← mul_assoc,
        mul_inv_cancel₀ (lt_of_lt_of_le one_pos hNR).ne', one_mul]
    calc (((normQ v : ℝ≥0) : ℝ)) ^ (m + 1) * (1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t * N⁻¹‖ ^ (m + 1)
        = (1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ((((normQ v : ℝ≥0) : ℝ)) ^ (m + 1) * ‖t * N⁻¹‖ ^ (m + 1)) := by
          ring
      _ = ((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t‖) * ‖t‖ ^ m := by rw [hNt, pow_succ']; ring

  have ht1 : ‖t‖ < 1 := by rw [ht, hA, hN]; exact hs

  have hOc : Oᶜ = ⋃ m : ℕ, negShell hπ m := compl_integers_eq_iUnion_negShell hπ
  have hsum : Summable fun m : ℕ => ∫ x in negShell hπ m, ‖g x‖ ∂μ := by
    rw [show (fun m : ℕ => ∫ x in negShell hπ m, ‖g x‖ ∂μ)
        = fun m : ℕ => ((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO * ‖t‖) * ‖t‖ ^ m from funext hnorm]
    exact (summable_geometric_of_lt_one (norm_nonneg _) ht1).mul_left _
  have hInt : IntegrableOn g Oᶜ μ := by
    rw [hOc]
    exact integrableOn_iUnion_of_summable_integral_norm (fun m => integrableOn_negShell μ hπ hχ _ m) hsum
  have htail : ∫ x in Oᶜ, g x ∂μ
      = (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * (1 - t)⁻¹) := by
    have h1 : HasSum (fun m : ℕ => ∫ x in negShell hπ m, g x ∂μ) (∫ x in Oᶜ, g x ∂μ) := by
      rw [hOc] at hInt ⊢
      exact hasSum_integral_iUnion (fun m => measurableSet_negShell hπ m) (negShell_disjoint hπ) hInt
    have h2 : HasSum (fun m : ℕ => (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * t ^ m))
        ((((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * (1 - t)⁻¹)) :=
      ((hasSum_geometric_of_norm_lt_one ht1).mul_left t).mul_left _
    rw [show (fun m : ℕ => ∫ x in negShell hπ m, g x ∂μ)
        = fun m : ℕ => (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * t ^ m) from funext hterm] at h1
    exact h1.unique h2

  have hOmeas : MeasurableSet O := (isCompact_integers (F := F) (v := v)).isClosed.measurableSet
  have hint1 : Integrable (O.indicator fun _ => (1 : ℂ)) μ :=
    (integrableOn_const ((measure_integers_lt_top' μ).ne)).integrable_indicator hOmeas
  have hint2 : Integrable (Oᶜ.indicator g) μ := hInt.integrable_indicator hOmeas.compl
  have h1t : (1 - t) ≠ 0 := by
    intro h0
    have : ‖t‖ = 1 := by rw [show t = 1 from (sub_eq_zero.mp h0).symm, norm_one]
    linarith
  have hw : (1 - t) * (1 - t)⁻¹ = 1 := mul_inv_cancel₀ h1t
  calc ∫ x, (O.indicator (fun _ => (1 : ℂ)) x + Oᶜ.indicator g x) ∂μ
      = (∫ x, O.indicator (fun _ => (1 : ℂ)) x ∂μ) + ∫ x, Oᶜ.indicator g x ∂μ := integral_add hint1 hint2
    _ = (μO : ℂ) + ∫ x in Oᶜ, g x ∂μ := by
        rw [integral_indicator_const (1 : ℂ) hOmeas, integral_indicator hOmeas.compl, Complex.real_smul,
          mul_one, hμO]
    _ = (μO : ℂ) + (((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ) : ℂ) * (t * (1 - t)⁻¹) := by rw [htail]
    _ = (μO : ℂ) + (1 - N⁻¹) * (μO : ℂ) * (t * (1 - t)⁻¹) := by
        have hC : ((((1 - (((normQ v : ℝ≥0) : ℝ))⁻¹) * μO : ℝ)) : ℂ) = (1 - N⁻¹) * (μO : ℂ) := by
          rw [← hQN]
          push_cast
          ring
        rw [hC]
    _ = (μO : ℂ) * (1 - A * N ^ (-(2 * s + 1))) * (1 - t)⁻¹ := by
        rw [hpow, ← mul_assoc A, ← ht]
        linear_combination (-(μO : ℂ)) * hw

end WeylGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
end M4aP2DGK.FinGK
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

end FinGKFold_Main
p2m_reactivate "P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK.LocalZetaUnramified P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.M4aP2DGK.FinGK"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
  M4aP2DGK.FinGK.WeylGK.integral_unramifiedWeylIntegrand_impl F v μ ϖ hϖ χ hχ s hs

#print axioms solution

end S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion (solution)
