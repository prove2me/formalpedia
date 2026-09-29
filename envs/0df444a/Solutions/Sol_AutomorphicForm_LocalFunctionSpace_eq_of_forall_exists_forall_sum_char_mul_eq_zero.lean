-- Prove2me | solution 1 for AutomorphicForm.LocalFunctionSpace.eq_of_forall_exists_forall_sum_char_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b1e7f59c-2693-5336-a406-2c10b2f23e8d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero

set_option autoImplicit false

open IsDedekindDomain

open scoped Classical

namespace WindowFourierAux

variable (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Γ" => Units (WithZero (Multiplicative ℤ))

private abbrev IsRepSystem (β δ : Γ) (T : Finset F) : Prop :=
  (∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) ∧
    ∀ x : F, Valued.v x < (β : WithZero (Multiplicative ℤ)) →
      ∃! t, t ∈ T ∧ Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ))

private abbrev factPrime (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

attribute [local instance] factPrime

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isCompact_integers : IsCompact {x : F | Valued.v x ≤ 1} := by
  haveI : CompactSpace (p.adicCompletionIntegers ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv p).symm.toContinuousLinearEquiv.toHomeomorph
      |>.compactSpace
  have h := isCompact_range (continuous_subtype_val (p := fun x : F => x ∈ p.adicCompletionIntegers ℚ))
  convert h using 1
  ext x
  simp [HeightOneSpectrum.mem_adicCompletionIntegers]

private theorem exists_valuation_eq (r : Γ) : ∃ c : F, Valued.v c = (r : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer' ℚ
  have hπ' : Valued.v (algebraMap (NumberField.RingOfIntegers ℚ) F π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) (v := p) π).trans hπ
  refine ⟨algebraMap (NumberField.RingOfIntegers ℚ) F π ^ (-WithZero.log (r : WithZero (Multiplicative ℤ))), ?_⟩
  rw [map_zpow₀, hπ', ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg,
    WithZero.exp_log r.ne_zero]

private theorem isOpen_unit_ball : IsOpen {x : F | Valued.v x < (1 : WithZero (Multiplicative ℤ))} := by
  have h := Valued.isOpen_ball (R := F) 1
  convert h using 1
  ext x
  simp [Valuation.restrict_lt_iff_lt_embedding]

private theorem isOpen_radiusBall (r : Γ) : IsOpen {x : F | Valued.v x < (r : WithZero (Multiplicative ℤ))} := by
  obtain ⟨c, hc⟩ := exists_valuation_eq p r
  have hset : {x : F | Valued.v x < (r : WithZero (Multiplicative ℤ))}
      = (fun x : F => c⁻¹ * x) ⁻¹' {y : F | Valued.v y < (1 : WithZero (Multiplicative ℤ))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, map_inv₀, hc]
    constructor
    · intro hx
      calc ((r : WithZero (Multiplicative ℤ)))⁻¹ * Valued.v x
          < ((r : WithZero (Multiplicative ℤ)))⁻¹ * (r : WithZero (Multiplicative ℤ)) :=
            mul_lt_mul_of_pos_left hx (zero_lt_iff.mpr (inv_ne_zero r.ne_zero))
        _ = 1 := inv_mul_cancel₀ r.ne_zero
    · intro hx
      have h := mul_lt_mul_of_pos_left hx (zero_lt_iff.mpr r.ne_zero)
      rwa [← mul_assoc, mul_inv_cancel₀ r.ne_zero, one_mul, mul_one] at h
  rw [hset]
  exact (isOpen_unit_ball p).preimage (continuous_const.mul continuous_id)

private theorem radiusBall_mem_nhds (y : F) (r : Γ) :
    {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} ∈ nhds y := by
  have hopen : IsOpen {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} :=
    (isOpen_radiusBall p r).preimage (continuous_id.sub continuous_const)
  exact hopen.mem_nhds (by simp)

private def closeSetoid (ρ : Γ) : Setoid F where
  r x y := Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ))
  iseqv :=
    { refl := fun x => by simp
      symm := fun {x y} h => by rw [Valuation.map_sub_swap]; exact h
      trans := fun {x y z} hxy hyz => by
        have : x - z = (x - y) + (y - z) := by ring
        rw [this]
        exact (Valuation.map_add _ _ _).trans_lt (max_lt hxy hyz) }

private theorem exists_isRepSystem (r₀ r₁ : Γ) (h : r₁ ≤ r₀) : ∃ T : Finset F, IsRepSystem p r₀ r₁ T := by
  have h' : (r₁ : WithZero (Multiplicative ℤ)) ≤ r₀ := Units.val_le_val.mpr h

  obtain ⟨c, hc⟩ := exists_valuation_eq p r₀
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact r₀.ne_zero hc.symm
  have hcompact : IsCompact ((fun x : F => c * x) '' {x : F | Valued.v x ≤ 1}) :=
    (isCompact_integers p).image (continuous_const.mul continuous_id)
  have hsub : {x : F | Valued.v x < (r₀ : WithZero (Multiplicative ℤ))} ⊆
      (fun x : F => c * x) '' {x : F | Valued.v x ≤ 1} := by
    intro x hx
    refine ⟨c⁻¹ * x, ?_, by simp [mul_inv_cancel_left₀ hc0]⟩
    simp only [Set.mem_setOf_eq, map_mul, map_inv₀, hc]
    have hx' : Valued.v x < (r₀ : WithZero (Multiplicative ℤ)) := hx
    have hr : (0 : WithZero (Multiplicative ℤ)) < ((r₀ : WithZero (Multiplicative ℤ)))⁻¹ :=
      zero_lt_iff.mpr (inv_ne_zero r₀.ne_zero)
    have := mul_lt_mul_of_pos_left hx' hr
    rw [inv_mul_cancel₀ r₀.ne_zero] at this
    exact this.le

  obtain ⟨T₀, -, hcover⟩ := hcompact.elim_nhds_subcover
    (fun y => {x : F | Valued.v (x - y) < (r₁ : WithZero (Multiplicative ℤ))}) (fun y _ => radiusBall_mem_nhds p y r₁)
  set T₁ : Finset F := T₀.filter (fun y => Valued.v y < (r₀ : WithZero (Multiplicative ℤ))) with hT₁
  have hnear : ∀ x : F, Valued.v x < (r₀ : WithZero (Multiplicative ℤ)) →
      ∃ y ∈ T₁, Valued.v (x - y) < (r₁ : WithZero (Multiplicative ℤ)) := by
    intro x hx
    have hxU := hcover (hsub hx)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hxU
    obtain ⟨y, hyT₀, hxy⟩ := hxU
    refine ⟨y, ?_, hxy⟩
    rw [hT₁, Finset.mem_filter]
    refine ⟨hyT₀, ?_⟩
    have hy : y = x - (x - y) := by ring
    rw [hy]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hx (hxy.trans_le h'))

  letI s : Setoid F := closeSetoid p r₁
  have hrel : ∀ x y : F, x ≈ y ↔ Valued.v (x - y) < (r₁ : WithZero (Multiplicative ℤ)) := fun _ _ => Iff.rfl
  refine ⟨(T₁.image (fun y => (⟦y⟧ : Quotient s))).image Quotient.out, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨y, hyT₁, rfl⟩ := Finset.mem_image.mp hq
    show Valued.v ((⟦y⟧ : Quotient s).out) < (r₀ : WithZero (Multiplicative ℤ))
    have hy : Valued.v y < (r₀ : WithZero (Multiplicative ℤ)) := (Finset.mem_filter.mp hyT₁).2
    have hout : Valued.v ((⟦y⟧ : Quotient s).out - y) < (r₁ : WithZero (Multiplicative ℤ)) :=
      (hrel _ _).mp (Quotient.mk_out y)
    have e : (⟦y⟧ : Quotient s).out = ((⟦y⟧ : Quotient s).out - y) + y := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (hout.trans_le h') hy)
  · intro x hx
    obtain ⟨y, hyT₁, hxy⟩ := hnear x hx
    have hxy' : x ≈ y := (hrel _ _).mpr hxy
    have hyt : y ≈ (⟦y⟧ : Quotient s).out := Setoid.symm (Quotient.mk_out y)
    refine ⟨(⟦y⟧ : Quotient s).out, ⟨?_, (hrel _ _).mp (Setoid.trans hxy' hyt)⟩, ?_⟩
    · exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hyT₁)
    · rintro t' ⟨ht', hxt'⟩
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp ht'
      have h1 : x ≈ q'.out := (hrel _ _).mpr hxt'
      have h2 : (⟦y⟧ : Quotient s).out ≈ q'.out := Setoid.trans (Setoid.symm (Setoid.trans hxy' hyt)) h1
      have h3 : (⟦y⟧ : Quotient s) = q' := by
        rw [← Quotient.out_eq (⟦y⟧ : Quotient s), ← Quotient.out_eq q']
        exact Quotient.sound h2
      rw [h3]

private theorem exists_conductor (χ : F → ℂ) (γ₀ : Γ)
    (hχ₁ : ∀ x : F, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1) (hχ₂ : ∃ x : F, χ x ≠ 1) :
    ∃ g : ℤ, (∀ z : F, Valued.v z < WithZero.exp g → χ z = 1) ∧
      ∃ w : F, w ≠ 0 ∧ WithZero.log (Valued.v w) ≤ g ∧ χ w ≠ 1 := by
  set b₀ : ℤ := WithZero.log (γ₀ : WithZero (Multiplicative ℤ)) with hb₀
  have hγ₀ : (γ₀ : WithZero (Multiplicative ℤ)) = WithZero.exp b₀ := (WithZero.exp_log γ₀.ne_zero).symm
  have hχ0 : χ 0 = 1 := hχ₁ 0 (by simp)

  have hex : ∃ j : ℕ, ∃ z : F, Valued.v z < WithZero.exp (b₀ + (j : ℤ)) ∧ χ z ≠ 1 := by
    obtain ⟨x₀, hx₀⟩ := hχ₂
    have hx₀0 : x₀ ≠ 0 := fun h => hx₀ (h ▸ hχ0)
    have hv0 : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
    refine ⟨(WithZero.log (Valued.v x₀) - b₀ + 1).toNat, x₀, ?_, hx₀⟩
    rw [← WithZero.log_lt_iff_lt_exp hv0]
    have := Int.self_le_toNat (WithZero.log (Valued.v x₀) - b₀ + 1)
    omega
  let j₁ := Nat.find hex
  have hj₁ : ∃ z : F, Valued.v z < WithZero.exp (b₀ + (j₁ : ℤ)) ∧ χ z ≠ 1 := Nat.find_spec hex
  have hj₁0 : j₁ ≠ 0 := by
    intro h0
    obtain ⟨z, hz, hz1⟩ := hj₁
    rw [h0] at hz
    exact hz1 (hχ₁ z (by rw [hγ₀]; simpa using hz))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj₁0
  refine ⟨b₀ + (k : ℤ), ?_, ?_⟩
  · intro z hz
    by_contra hz1
    have hlt : k < j₁ := by omega
    exact Nat.find_min hex hlt ⟨z, hz, hz1⟩
  · obtain ⟨w, hw, hw1⟩ := hj₁
    have hw0 : w ≠ 0 := fun h => hw1 (h ▸ hχ0)
    refine ⟨w, hw0, ?_, hw1⟩
    have hvw : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw0
    rw [hk, ← WithZero.log_lt_iff_lt_exp hvw] at hw
    push_cast at hw
    omega

private theorem exists_forall_char_mul_eq_one_iff (χ : F → ℂ) (γ₀ : Γ)
    (hχ₁ : ∀ x : F, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1) (hχ₂ : ∃ x : F, χ x ≠ 1)
    (δ : Γ) :
    ∃ r₀ : Γ, ∀ c : F,
      (∀ y : F, Valued.v y < (r₀ : WithZero (Multiplicative ℤ)) → χ (c * y) = 1) ↔
        Valued.v c < (δ : WithZero (Multiplicative ℤ)) := by
  have hχ0 : χ 0 = 1 := hχ₁ 0 (by simp)
  obtain ⟨g, hg, w, hw0, hwg, hw1⟩ := exists_conductor p χ γ₀ hχ₁ hχ₂
  set d : ℤ := WithZero.log (δ : WithZero (Multiplicative ℤ)) with hd
  have hδ : (δ : WithZero (Multiplicative ℤ)) = WithZero.exp d := (WithZero.exp_log δ.ne_zero).symm
  refine ⟨WithZero.expEquiv (g - d + 1), fun c => ⟨fun h => ?_, fun hc y hy => ?_⟩⟩
  ·
    by_contra hcd
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hcd (by rw [map_zero]; exact zero_lt_iff.mpr δ.ne_zero)
    have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hdc : d ≤ WithZero.log (Valued.v c) := by
      rw [hδ, not_lt] at hcd
      exact WithZero.le_log_of_exp_le hcd
    have hvw : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw0
    have hy : Valued.v (c⁻¹ * w) < ((WithZero.expEquiv (g - d + 1) : Γ) : WithZero (Multiplicative ℤ)) := by
      have hvy : Valued.v (c⁻¹ * w) ≠ 0 := (Valuation.ne_zero_iff _).mpr (mul_ne_zero (inv_ne_zero hc0) hw0)
      rw [WithZero.coe_expEquiv_apply, ← WithZero.log_lt_iff_lt_exp hvy, map_mul, map_inv₀,
        WithZero.log_mul (inv_ne_zero hvc) hvw, WithZero.log_inv]
      omega
    have := h _ hy
    rw [mul_inv_cancel_left₀ hc0] at this
    exact hw1 this
  ·
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_mul]; exact hχ0
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [mul_zero]; exact hχ0
    apply hg
    have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    rw [hδ, ← WithZero.log_lt_iff_lt_exp hvc] at hc
    rw [WithZero.coe_expEquiv_apply, ← WithZero.log_lt_iff_lt_exp hvy] at hy
    rw [map_mul, ← WithZero.log_lt_iff_lt_exp (mul_ne_zero hvc hvy), WithZero.log_mul hvc hvy]
    omega

private theorem isRepSystem_image_add {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) {y : F}
    (hy : Valued.v y < (β : WithZero (Multiplicative ℤ))) : IsRepSystem p β δ (T.image (· + y)) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (hT.1 t ht) hy)
  · intro x hx
    have hxy : Valued.v (x - y) < (β : WithZero (Multiplicative ℤ)) :=
      (Valuation.map_sub _ _ _).trans_lt (max_lt hx hy)
    obtain ⟨t, ⟨ht, hclose⟩, huniq⟩ := hT.2 (x - y) hxy
    refine ⟨t + y, ⟨Finset.mem_image_of_mem _ ht, ?_⟩, ?_⟩
    · have e : x - (t + y) = x - y - t := by ring
      rw [e]
      exact hclose
    · rintro s ⟨hs, hs'⟩
      obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hs
      have e : x - y - t₁ = x - (t₁ + y) := by ring
      rw [huniq t₁ ⟨ht₁, by rw [e]; exact hs'⟩]

private theorem sum_ite_eq_of_isRepSystem {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) (φ : F → ℂ)
    (hφ : ∀ x y : F, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → φ x = φ y) {x : F}
    (hx : Valued.v x < (β : WithZero (Multiplicative ℤ))) :
    (∑ t ∈ T, if Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ)) then φ t else 0) = φ x := by
  obtain ⟨t, ⟨ht, hclose⟩, huniq⟩ := hT.2 x hx
  rw [Finset.sum_eq_single_of_mem t ht]
  · rw [if_pos hclose, hφ x t hclose]
  · intro u hu hne
    exact if_neg fun hc => hne (huniq u ⟨hu, hc⟩)

private theorem sum_eq_sum_of_isRepSystem {β δ : Γ} {T T' : Finset F} (hT : IsRepSystem p β δ T)
    (hT' : IsRepSystem p β δ T') (φ : F → ℂ)
    (hφ : ∀ x y : F, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → φ x = φ y) :
    ∑ t ∈ T, φ t = ∑ t ∈ T', φ t := by
  calc ∑ t ∈ T, φ t
      = ∑ t ∈ T, ∑ t' ∈ T', (if Valued.v (t - t') < (δ : WithZero (Multiplicative ℤ)) then φ t' else 0) :=
        Finset.sum_congr rfl fun t ht => (sum_ite_eq_of_isRepSystem p hT' φ hφ (hT.1 t ht)).symm
    _ = ∑ t' ∈ T', ∑ t ∈ T, (if Valued.v (t - t') < (δ : WithZero (Multiplicative ℤ)) then φ t' else 0) :=
        Finset.sum_comm
    _ = ∑ t' ∈ T', ∑ t ∈ T, (if Valued.v (t' - t) < (δ : WithZero (Multiplicative ℤ)) then φ t else 0) := by
        refine Finset.sum_congr rfl fun t' _ => Finset.sum_congr rfl fun t _ => ?_
        rw [Valuation.map_sub_swap]
        split_ifs with h
        · exact hφ t' t h
        · rfl
    _ = ∑ t' ∈ T', φ t' :=
        Finset.sum_congr rfl fun t' ht' => sum_ite_eq_of_isRepSystem p hT φ hφ (hT'.1 t' ht')

private theorem sum_char_eq_zero (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) {β δ : Γ} {T : Finset F}
    (hT : IsRepSystem p β δ T) (c : F)
    (hsmall : ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) → χ (c * z) = 1)
    (hbig : ∃ y : F, Valued.v y < (β : WithZero (Multiplicative ℤ)) ∧ χ (c * y) ≠ 1) :
    ∑ x ∈ T, χ (c * x) = 0 := by
  obtain ⟨y, hy, hy1⟩ := hbig
  have hconst : ∀ x x' : F, Valued.v (x - x') < (δ : WithZero (Multiplicative ℤ)) → χ (c * x) = χ (c * x') := by
    intro x x' hxx'
    have e : c * x = c * x' + c * (x - x') := by ring
    rw [e, hχ, hsmall _ hxx', mul_one]
  have h1 : ∑ x ∈ T, χ (c * x) = ∑ x ∈ T.image (· + y), χ (c * x) :=
    sum_eq_sum_of_isRepSystem p hT (isRepSystem_image_add p hT hy) _ hconst
  have h2 : ∑ x ∈ T.image (· + y), χ (c * x) = χ (c * y) * ∑ x ∈ T, χ (c * x) := by
    rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_add, hχ, mul_comm]
  have h3 : (χ (c * y) - 1) * ∑ x ∈ T, χ (c * x) = 0 := by
    rw [sub_mul, one_mul, ← h2, ← h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) hy1
  · exact h

private theorem sum_char_eq_ite (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) {β ρ r₀ s : Γ}
    (hr₀ : ∀ u : F, (∀ y : F, Valued.v y < (r₀ : WithZero (Multiplicative ℤ)) → χ (u * y) = 1) ↔
      Valued.v u < (ρ : WithZero (Multiplicative ℤ)))
    (hs : ∀ u : F, Valued.v u < (β : WithZero (Multiplicative ℤ)) →
      ∀ z : F, Valued.v z < (s : WithZero (Multiplicative ℤ)) → χ (u * z) = 1)
    {Y : Finset F} (hY : IsRepSystem p r₀ s Y) (u : F) (hu : Valued.v u < (β : WithZero (Multiplicative ℤ))) :
    ∑ y ∈ Y, χ (u * y) = if Valued.v u < (ρ : WithZero (Multiplicative ℤ)) then (Y.card : ℂ) else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl (fun y hy => (hr₀ u).mpr h y (hY.1 y hy)), Finset.sum_const, nsmul_eq_mul, mul_one]
  · refine sum_char_eq_zero p χ hχ hY u (hs u hu) ?_
    by_contra hcon
    push Not at hcon
    exact h ((hr₀ u).mp hcon)

private theorem close_trans {δ : Γ} {a b c : F} (h₁ : Valued.v (a - b) < (δ : WithZero (Multiplicative ℤ)))
    (h₂ : Valued.v (b - c) < (δ : WithZero (Multiplicative ℤ))) :
    Valued.v (a - c) < (δ : WithZero (Multiplicative ℤ)) := by
  have e : a - c = (a - b) + (b - c) := by ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h₁ h₂)

private theorem isRepSystem_insert_erase {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) {t : F} (ht : t ∈ T)
    {t₁ : F} (h₁ : Valued.v t₁ < (β : WithZero (Multiplicative ℤ)))
    (hclose : Valued.v (t₁ - t) < (δ : WithZero (Multiplicative ℤ))) :
    IsRepSystem p β δ (insert t₁ (T.erase t)) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with hs | hs
    · rw [hs]; exact h₁
    · exact hT.1 s (Finset.mem_of_mem_erase hs)
  · intro x hx
    obtain ⟨r, ⟨hrT, hxr⟩, hruniq⟩ := hT.2 x hx
    by_cases hrt : r = t
    · refine ⟨t₁, ⟨Finset.mem_insert_self _ _, ?_⟩, ?_⟩
      · rw [hrt] at hxr
        exact close_trans p hxr (by rw [Valuation.map_sub_swap]; exact hclose)
      · rintro y ⟨hy, hxy⟩
        rcases Finset.mem_insert.mp hy with hy | hy
        · exact hy
        · exfalso
          have hyr := hruniq y ⟨Finset.mem_of_mem_erase hy, hxy⟩
          exact Finset.ne_of_mem_erase hy (hyr.trans hrt)
    · refine ⟨r, ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hrt, hrT⟩), hxr⟩, ?_⟩
      rintro y ⟨hy, hxy⟩
      rcases Finset.mem_insert.mp hy with hy | hy
      · exfalso
        apply hrt
        rw [hy] at hxy
        exact (hruniq t ⟨ht, close_trans p hxy hclose⟩).symm
      · exact hruniq y ⟨Finset.mem_of_mem_erase hy, hxy⟩

private theorem eq_of_forall_isRepSystem_sum_eq_zero {β δ : Γ} (hδβ : δ ≤ β) (g : F → ℂ)
    (h : ∀ T : Finset F, IsRepSystem p β δ T → ∑ t ∈ T, g t = 0) {t₁ t₂ : F}
    (h₁ : Valued.v t₁ < (β : WithZero (Multiplicative ℤ))) (h₂ : Valued.v t₂ < (β : WithZero (Multiplicative ℤ)))
    (h₁₂ : Valued.v (t₁ - t₂) < (δ : WithZero (Multiplicative ℤ))) : g t₁ = g t₂ := by
  obtain ⟨T, hT⟩ := exists_isRepSystem p β δ hδβ
  obtain ⟨t, ⟨htT, h₁t⟩, huniq⟩ := hT.2 t₁ h₁
  have h₂t : Valued.v (t₂ - t) < (δ : WithZero (Multiplicative ℤ)) :=
    close_trans p (by rw [Valuation.map_sub_swap]; exact h₁₂) h₁t
  have hS₁ := h _ (isRepSystem_insert_erase p hT htT h₁ h₁t)
  have hS₂ := h _ (isRepSystem_insert_erase p hT htT h₂ h₂t)
  have hn₁ : t₁ ∉ T.erase t := fun hmem =>
    Finset.ne_of_mem_erase hmem (huniq t₁ ⟨Finset.mem_of_mem_erase hmem, by simp⟩)
  have hn₂ : t₂ ∉ T.erase t := fun hmem =>
    Finset.ne_of_mem_erase hmem (huniq t₂ ⟨Finset.mem_of_mem_erase hmem, h₁₂⟩)
  rw [Finset.sum_insert hn₁] at hS₁
  rw [Finset.sum_insert hn₂] at hS₂
  linear_combination hS₁ - hS₂

private theorem isRepSystem_filter_sub {β ρ δ : Γ} (hδρ : δ ≤ ρ) (hρβ : ρ ≤ β) {T₁ : Finset F}
    (h₁ : IsRepSystem p β δ T₁) {t' : F} (ht' : Valued.v t' < (β : WithZero (Multiplicative ℤ))) :
    IsRepSystem p ρ δ ((T₁.filter fun t => Valued.v (t - t') < (ρ : WithZero (Multiplicative ℤ))).image (· - t')) := by
  have hδρ' : (δ : WithZero (Multiplicative ℤ)) ≤ ρ := Units.val_le_val.mpr hδρ
  have hρβ' : (ρ : WithZero (Multiplicative ℤ)) ≤ β := Units.val_le_val.mpr hρβ
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp ht).2
  · intro y hy
    have hx : Valued.v (y + t') < (β : WithZero (Multiplicative ℤ)) :=
      (Valuation.map_add _ _ _).trans_lt (max_lt (hy.trans_le hρβ') ht')
    obtain ⟨t, ⟨htT, hxt⟩, huniq⟩ := h₁.2 (y + t') hx
    have htclose : Valued.v (t - t') < (ρ : WithZero (Multiplicative ℤ)) := by
      have e : t - t' = y - (y + t' - t) := by ring
      rw [e]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt hy (hxt.trans_le hδρ'))
    refine ⟨t - t', ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htT, htclose⟩, rfl⟩, ?_⟩, ?_⟩
    · have e : y - (t - t') = y + t' - t := by ring
      rw [e]
      exact hxt
    · rintro z ⟨hz, hyz⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      have hs' : Valued.v (y + t' - s) < (δ : WithZero (Multiplicative ℤ)) := by
        have e : y + t' - s = y - (s - t') := by ring
        rw [e]
        exact hyz
      rw [huniq s ⟨(Finset.mem_filter.mp hs).1, hs'⟩]

private theorem count_filter_eq_count {β ρ δ : Γ} (hδρ : δ ≤ ρ) (hρβ : ρ ≤ β) {T₁ N : Finset F}
    (h₁ : IsRepSystem p β δ T₁) (hN : IsRepSystem p ρ δ N) {t' : F}
    (ht' : Valued.v t' < (β : WithZero (Multiplicative ℤ))) :
    (T₁.filter fun t => Valued.v (t - t') < (ρ : WithZero (Multiplicative ℤ))).card = N.card := by
  have hsum := sum_eq_sum_of_isRepSystem p (isRepSystem_filter_sub p hδρ hρβ h₁ ht') hN (fun _ => (1 : ℂ))
    (fun _ _ _ => rfl)
  rw [Finset.sum_const, Finset.sum_const, Finset.card_image_of_injective _ sub_left_injective] at hsum
  simpa using hsum

private theorem sum_eq_count_mul_sum {β ρ δ : Γ} (hδρ : δ ≤ ρ) (hρβ : ρ ≤ β) {T₁ T₂ N : Finset F}
    (h₁ : IsRepSystem p β δ T₁) (h₂ : IsRepSystem p β ρ T₂) (hN : IsRepSystem p ρ δ N) (g : F → ℂ)
    (hg : ∀ x y : F, Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ)) → g x = g y) :
    ∑ t ∈ T₁, g t = (N.card : ℂ) * ∑ t ∈ T₂, g t := by
  calc ∑ t ∈ T₁, g t
      = ∑ t ∈ T₁, ∑ t' ∈ T₂, (if Valued.v (t - t') < (ρ : WithZero (Multiplicative ℤ)) then g t' else 0) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [sum_ite_eq_of_isRepSystem p h₂ g hg (h₁.1 t ht)]
    _ = ∑ t' ∈ T₂, ∑ t ∈ T₁, (if Valued.v (t - t') < (ρ : WithZero (Multiplicative ℤ)) then g t' else 0) :=
        Finset.sum_comm
    _ = ∑ t' ∈ T₂, ((T₁.filter fun t => Valued.v (t - t') < (ρ : WithZero (Multiplicative ℤ))).card : ℂ) * g t' := by
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t' ∈ T₂, (N.card : ℂ) * g t' := by
        refine Finset.sum_congr rfl fun t' ht' => ?_
        rw [count_filter_eq_count p hδρ hρβ h₁ hN (h₂.1 t' ht')]
    _ = (N.card : ℂ) * ∑ t ∈ T₂, g t := by rw [Finset.mul_sum]

private theorem sum_eq_zero_of_forall_isRepSystem {β ρ : Γ} (hρβ : ρ ≤ β) (δ : Γ) (g : F → ℂ)
    (hg : ∀ x y : F, Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ)) → g x = g y)
    (h : ∀ T : Finset F, IsRepSystem p β δ T → ∑ t ∈ T, g t = 0) {T : Finset F}
    (hT : IsRepSystem p β ρ T) : ∑ t ∈ T, g t = 0 := by
  rcases le_or_gt δ ρ with hδρ | hρδ
  · obtain ⟨N, hN⟩ := exists_isRepSystem p ρ δ hδρ
    obtain ⟨T₁, hT₁⟩ := exists_isRepSystem p β δ (hδρ.trans hρβ)
    have hidx := sum_eq_count_mul_sum p hδρ hρβ hT₁ hT hN g hg
    rw [h T₁ hT₁] at hidx
    have hNcard : (N.card : ℂ) ≠ 0 := by
      have hne : N.Nonempty := by
        obtain ⟨t, ⟨ht, -⟩, -⟩ := hN.2 0 (by simp)
        exact ⟨t, ht⟩
      exact_mod_cast hne.card_pos.ne'
    rcases mul_eq_zero.mp hidx.symm with h0 | h0
    · exact absurd h0 hNcard
    · exact h0
  · rcases le_or_gt δ β with hδβ | hβδ
    · set g' : F → ℂ := fun x => if Valued.v x < (β : WithZero (Multiplicative ℤ)) then g x else 0 with hg'
      have hg'win : ∀ x : F, Valued.v x < (β : WithZero (Multiplicative ℤ)) → g' x = g x := fun x hx => by
        simp [hg', hx]
      have hsum' : ∀ T' : Finset F, IsRepSystem p β δ T' → ∑ t ∈ T', g' t = 0 := by
        intro T' hT'
        rw [← h T' hT']
        exact Finset.sum_congr rfl fun t ht => hg'win t (hT'.1 t ht)
      have hδβ' : (δ : WithZero (Multiplicative ℤ)) ≤ β := Units.val_le_val.mpr hδβ
      have hg'const : ∀ x y : F, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → g' x = g' y := by
        intro x y hxy
        by_cases hx : Valued.v x < (β : WithZero (Multiplicative ℤ))
        · have hy : Valued.v y < (β : WithZero (Multiplicative ℤ)) := by
            have e : y = x - (x - y) := by ring
            rw [e]
            exact (Valuation.map_sub _ _ _).trans_lt (max_lt hx (hxy.trans_le hδβ'))
          rw [hg'win x hx, hg'win y hy]
          exact eq_of_forall_isRepSystem_sum_eq_zero p hδβ g h hx hy hxy
        · have hy : ¬ Valued.v y < (β : WithZero (Multiplicative ℤ)) := by
            intro hy
            apply hx
            have e : x = y + (x - y) := by ring
            rw [e]
            exact (Valuation.map_add _ _ _).trans_lt (max_lt hy (hxy.trans_le hδβ'))
          simp [hg', hx, hy]
      obtain ⟨N, hN⟩ := exists_isRepSystem p δ ρ hρδ.le
      obtain ⟨T₂, hT₂⟩ := exists_isRepSystem p β δ hδβ
      have hidx := sum_eq_count_mul_sum p hρδ.le hδβ hT hT₂ hN g' hg'const
      rw [hsum' T₂ hT₂, mul_zero] at hidx
      exact (Finset.sum_congr rfl fun t ht => (hg'win t (hT.1 t ht)).symm).trans hidx
    · apply Finset.sum_eq_zero
      intro t ht
      have hβδ' : (β : WithZero (Multiplicative ℤ)) < δ := Units.val_lt_val.mpr hβδ
      have hsys : IsRepSystem p β δ {t} := by
        refine ⟨fun s hs => ?_, fun x hx => ?_⟩
        · rw [Finset.mem_singleton.mp hs]
          exact hT.1 t ht
        · refine ⟨t, ⟨Finset.mem_singleton_self t, ?_⟩, ?_⟩
          · exact (Valuation.map_sub _ _ _).trans_lt (max_lt (hx.trans hβδ') ((hT.1 t ht).trans hβδ'))
          · rintro y ⟨hy, -⟩
            exact Finset.mem_singleton.mp hy
      simpa using h {t} hsys

private theorem char_mul_eq_one_iff_of_conductor (χ : F → ℂ) (hχ0 : χ 0 = 1) {g : ℤ}
    (hg : ∀ z : F, Valued.v z < WithZero.exp g → χ z = 1) {w : F} (hw0 : w ≠ 0)
    (hwg : WithZero.log (Valued.v w) ≤ g) (hw1 : χ w ≠ 1) (R : ℤ) (c : F) :
    (∀ y : F, Valued.v y < WithZero.exp R → χ (c * y) = 1) ↔ Valued.v c < WithZero.exp (g - R + 1) := by
  refine ⟨fun h => ?_, fun hc y hy => ?_⟩
  · by_contra hcd
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hcd (by rw [map_zero]; exact WithZero.exp_pos)
    have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hdc : g - R + 1 ≤ WithZero.log (Valued.v c) := WithZero.le_log_of_exp_le (not_lt.mp hcd)
    have hvw : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw0
    have hy : Valued.v (c⁻¹ * w) < WithZero.exp R := by
      have hvy : Valued.v (c⁻¹ * w) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (mul_ne_zero (inv_ne_zero hc0) hw0)
      rw [← WithZero.log_lt_iff_lt_exp hvy, map_mul, map_inv₀, WithZero.log_mul (inv_ne_zero hvc) hvw,
        WithZero.log_inv]
      omega
    have := h _ hy
    rw [mul_inv_cancel_left₀ hc0] at this
    exact hw1 this
  · rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_mul]; exact hχ0
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [mul_zero]; exact hχ0
    apply hg
    have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    rw [← WithZero.log_lt_iff_lt_exp hvc] at hc
    rw [← WithZero.log_lt_iff_lt_exp hvy] at hy
    rw [map_mul, ← WithZero.log_lt_iff_lt_exp (mul_ne_zero hvc hvy), WithZero.log_mul hvc hvy]
    omega

private theorem isRepSystem_filter_window {β β' ρ : Γ} (hρβ : ρ ≤ β) (hββ' : β ≤ β') {T' : Finset F}
    (hT' : IsRepSystem p β' ρ T') :
    IsRepSystem p β ρ (T'.filter fun t => Valued.v t < (β : WithZero (Multiplicative ℤ))) := by
  have hρβ' : (ρ : WithZero (Multiplicative ℤ)) ≤ β := Units.val_le_val.mpr hρβ
  refine ⟨fun t ht => (Finset.mem_filter.mp ht).2, fun x hx => ?_⟩
  obtain ⟨t, ⟨htT, hxt⟩, huniq⟩ := hT'.2 x (hx.trans_le (Units.val_le_val.mpr hββ'))
  have htβ : Valued.v t < (β : WithZero (Multiplicative ℤ)) := by
    have e : t = x - (x - t) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hx (hxt.trans_le hρβ'))
  refine ⟨t, ⟨Finset.mem_filter.mpr ⟨htT, htβ⟩, hxt⟩, ?_⟩
  rintro s ⟨hs, hxs⟩
  exact huniq s ⟨(Finset.mem_filter.mp hs).1, hxs⟩

private theorem twisted_const (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) (f : F → ℂ) {ρ : Γ}
    (hf : ∀ x y : F, Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ)) → f x = f y) {a : F}
    (hkill : ∀ z : F, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (a * z) = 1) (x y : F)
    (hxy : Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ))) : χ (-(a * x)) * f x = χ (-(a * y)) * f y := by
  have e : -(a * x) = -(a * y) + a * (-(x - y)) := by ring
  have hz : Valued.v (-(x - y)) < (ρ : WithZero (Multiplicative ℤ)) := by rw [Valuation.map_neg]; exact hxy
  rw [hf x y hxy, e, hχ, hkill _ hz, mul_one]

private theorem sum_twisted_add_eq (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) (f : F → ℂ) {β : Γ}
    {T : Finset F} (hTβ : ∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) (a : F) {k : F}
    (hk : ∀ y : F, Valued.v y < (β : WithZero (Multiplicative ℤ)) → χ (k * y) = 1) :
    ∑ t ∈ T, χ (-((a + k) * t)) * f t = ∑ t ∈ T, χ (-(a * t)) * f t := by
  refine Finset.sum_congr rfl fun t ht => ?_
  have e : -((a + k) * t) = -(a * t) + k * (-t) := by ring
  have hnt : Valued.v (-t) < (β : WithZero (Multiplicative ℤ)) := by rw [Valuation.map_neg]; exact hTβ t ht
  rw [e, hχ, hk _ hnt, mul_one]

private theorem sum_sum_twisted_eq_count_mul (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) (f : F → ℂ)
    {β β' ρ α α' : Γ} (hρβ : ρ ≤ β) (hββ' : β ≤ β')
    (hdual : ∀ c : F, (∀ y : F, Valued.v y < (α : WithZero (Multiplicative ℤ)) → χ (c * y) = 1) ↔
      Valued.v c < (β : WithZero (Multiplicative ℤ)))
    (hdual' : ∀ c : F, (∀ y : F, Valued.v y < (α' : WithZero (Multiplicative ℤ)) → χ (c * y) = 1) ↔
      Valued.v c < (β' : WithZero (Multiplicative ℤ)))
    {K : Finset F} (hK : IsRepSystem p α α' K) {T T' : Finset F} (hT : IsRepSystem p β ρ T)
    (hT' : IsRepSystem p β' ρ T') (a : F)
    (hconst : ∀ x y : F, Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ)) →
      χ (-(a * x)) * f x = χ (-(a * y)) * f y) :
    ∑ k ∈ K, ∑ t ∈ T', χ (-((a + k) * t)) * f t = (K.card : ℂ) * ∑ t ∈ T, χ (-(a * t)) * f t := by

  have hinner : ∀ t ∈ T',
      ∑ k ∈ K, χ (-t * k) = if Valued.v t < (β : WithZero (Multiplicative ℤ)) then (K.card : ℂ) else 0 := by
    intro t ht
    have hnt' : Valued.v (-t) < (β' : WithZero (Multiplicative ℤ)) := by rw [Valuation.map_neg]; exact hT'.1 t ht
    split_ifs with htβ
    · have hnt : Valued.v (-t) < (β : WithZero (Multiplicative ℤ)) := by rw [Valuation.map_neg]; exact htβ
      rw [Finset.sum_congr rfl (fun k hk => (hdual (-t)).mpr hnt k (hK.1 k hk)), Finset.sum_const, nsmul_eq_mul,
        mul_one]
    · refine sum_char_eq_zero p χ hχ hK (-t) ((hdual' (-t)).mpr hnt') ?_
      by_contra hcon
      push Not at hcon
      have := (hdual (-t)).mp hcon
      rw [Valuation.map_neg] at this
      exact htβ this
  calc ∑ k ∈ K, ∑ t ∈ T', χ (-((a + k) * t)) * f t
      = ∑ t ∈ T', (χ (-(a * t)) * f t) * ∑ k ∈ K, χ (-t * k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have e : -((a + k) * t) = -(a * t) + -t * k := by ring
        rw [e, hχ]
        ring
    _ = ∑ t ∈ T',
          if Valued.v t < (β : WithZero (Multiplicative ℤ)) then (χ (-(a * t)) * f t) * (K.card : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [hinner t ht]
        split_ifs <;> simp
    _ = ∑ t ∈ T'.filter (fun t => Valued.v t < (β : WithZero (Multiplicative ℤ))),
          (χ (-(a * t)) * f t) * (K.card : ℂ) := by
        rw [Finset.sum_filter]
    _ = (K.card : ℂ) *
          ∑ t ∈ T'.filter (fun t => Valued.v t < (β : WithZero (Multiplicative ℤ))), χ (-(a * t)) * f t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ = (K.card : ℂ) * ∑ t ∈ T, χ (-(a * t)) * f t := by
        rw [sum_eq_sum_of_isRepSystem p (isRepSystem_filter_window p hρβ hββ' hT') hT _ hconst]

private theorem exists_unit_gt (y : F) : ∃ β₀ : Γ, Valued.v y < (β₀ : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨1, by simp⟩
  · have hv : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hy
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hv
    refine ⟨Units.mk0 ((m * Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      WithZero.coe_ne_zero, ?_⟩
    rw [← hm, Units.val_mk0, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_ofAdd]
    exact lt_add_one _

private theorem exists_isCompact_of_radius (r : Γ) :
    ∃ K : Set F, IsCompact K ∧ ∀ x : F, Valued.v x < (r : WithZero (Multiplicative ℤ)) → x ∈ K := by
  obtain ⟨c, hc⟩ := exists_valuation_eq p r
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact r.ne_zero hc.symm
  refine ⟨(fun x : F => c * x) '' {x : F | Valued.v x ≤ 1},
    (isCompact_integers p).image (continuous_const.mul continuous_id), fun x hx => ?_⟩
  refine ⟨c⁻¹ * x, ?_, by simp [mul_inv_cancel_left₀ hc0]⟩
  simp only [Set.mem_setOf_eq, map_mul, map_inv₀, hc]
  have hr : (0 : WithZero (Multiplicative ℤ)) < ((r : WithZero (Multiplicative ℤ)))⁻¹ :=
    zero_lt_iff.mpr (inv_ne_zero r.ne_zero)
  have := mul_lt_mul_of_pos_left hx hr
  rw [inv_mul_cancel₀ r.ne_zero] at this
  exact this.le

private theorem eq_inv_count_mul_sum_twisted (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) (f : F → ℂ)
    {β ρ r₀ s : Γ}
    (hr₀ : ∀ u : F, (∀ y : F, Valued.v y < (r₀ : WithZero (Multiplicative ℤ)) → χ (u * y) = 1) ↔
      Valued.v u < (ρ : WithZero (Multiplicative ℤ)))
    (hs : ∀ u : F, Valued.v u < (β : WithZero (Multiplicative ℤ)) →
      ∀ z : F, Valued.v z < (s : WithZero (Multiplicative ℤ)) → χ (u * z) = 1)
    {Y : Finset F} (hY : IsRepSystem p r₀ s Y) {T : Finset F} (hT : IsRepSystem p β ρ T)
    (hf : ∀ x y : F, Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ)) → f x = f y) {u : F}
    (hu : Valued.v u < (β : WithZero (Multiplicative ℤ))) :
    f u = (Y.card : ℂ)⁻¹ * ∑ a ∈ Y, χ (u * a) * ∑ t ∈ T, χ (-(a * t)) * f t := by
  have hYcard : (Y.card : ℂ) ≠ 0 := by
    obtain ⟨a, ⟨ha, -⟩, -⟩ := hY.2 0 (by simp)
    exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩).ne'
  have hchar : ∀ t a : F, χ ((u - t) * a) = χ (u * a) * χ (-(a * t)) := by
    intro t a
    rw [← hχ]
    congr 1
    ring
  calc f u
      = ∑ t ∈ T, if Valued.v (u - t) < (ρ : WithZero (Multiplicative ℤ)) then f t else 0 :=
        (sum_ite_eq_of_isRepSystem p hT f hf hu).symm
    _ = ∑ t ∈ T, (Y.card : ℂ)⁻¹ * (f t * ∑ a ∈ Y, χ ((u - t) * a)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hut : Valued.v (u - t) < (β : WithZero (Multiplicative ℤ)) :=
          (Valuation.map_sub _ _ _).trans_lt (max_lt hu (hT.1 t ht))
        rw [sum_char_eq_ite p χ hχ hr₀ hs hY (u - t) hut]
        split_ifs
        · rw [mul_comm (f t), ← mul_assoc, inv_mul_cancel₀ hYcard, one_mul]
        · rw [mul_zero, mul_zero]
    _ = (Y.card : ℂ)⁻¹ * ∑ t ∈ T, ∑ a ∈ Y, χ (u * a) * (χ (-(a * t)) * f t) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hchar]
        ring
    _ = (Y.card : ℂ)⁻¹ * ∑ a ∈ Y, χ (u * a) * ∑ t ∈ T, χ (-(a * t)) * f t := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

private theorem exists_sum_twisted_ne_zero (χ : F → ℂ) (hχ : ∀ x y : F, χ (x + y) = χ x * χ y) (f : F → ℂ)
    {β ρ r₀ s : Γ}
    (hr₀ : ∀ u : F, (∀ y : F, Valued.v y < (r₀ : WithZero (Multiplicative ℤ)) → χ (u * y) = 1) ↔
      Valued.v u < (ρ : WithZero (Multiplicative ℤ)))
    (hs : ∀ u : F, Valued.v u < (β : WithZero (Multiplicative ℤ)) →
      ∀ z : F, Valued.v z < (s : WithZero (Multiplicative ℤ)) → χ (u * z) = 1)
    {Y : Finset F} (hY : IsRepSystem p r₀ s Y) {T : Finset F} (hT : IsRepSystem p β ρ T)
    (hf : ∀ x y : F, Valued.v (x - y) < (ρ : WithZero (Multiplicative ℤ)) → f x = f y) {x y : F}
    (hx : Valued.v x < (β : WithZero (Multiplicative ℤ))) (hy : Valued.v y < (β : WithZero (Multiplicative ℤ)))
    (hne : f x ≠ f y) :
    ∃ a ∈ Y, (∑ t ∈ T, χ (-(a * t)) * f t) ≠ 0 ∧
      ¬ ∀ z : F, Valued.v z < (β : WithZero (Multiplicative ℤ)) → χ (a * z) = 1 := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [eq_inv_count_mul_sum_twisted p χ hχ f hr₀ hs hY hT hf hx,
    eq_inv_count_mul_sum_twisted p χ hχ f hr₀ hs hY hT hf hy]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hFa : (∑ t ∈ T, χ (-(a * t)) * f t) = 0
  · rw [hFa, mul_zero, mul_zero]
  · have hkill := hcon a ha hFa
    rw [mul_comm x a, mul_comm y a, hkill x hx, hkill y hy]

end WindowFourierAux

open WindowFourierAux in

theorem solution
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (f : p.adicCompletion ℚ → ℂ)
    (hf : ∃ δ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x y : p.adicCompletion ℚ, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → f x = f y)
    (χ : p.adicCompletion ℚ → ℂ)
    (hχ : ∀ x y : p.adicCompletion ℚ, χ (x + y) = χ x * χ y)
    (hχ₁ : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : p.adicCompletion ℚ, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1)
    (hχ₂ : ∃ x₀ : p.adicCompletion ℚ, χ x₀ ≠ 1)
    (hsum : ∀ a : p.adicCompletion ℚ, a ≠ 0 →
      ∃ β₀ : (WithZero (Multiplicative ℤ))ˣ, ∀ β : (WithZero (Multiplicative ℤ))ˣ, β₀ ≤ β →
      ∃ δ : (WithZero (Multiplicative ℤ))ˣ, ∀ T : Finset (p.adicCompletion ℚ),
        (∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) →
        (∀ x : p.adicCompletion ℚ, Valued.v x < (β : WithZero (Multiplicative ℤ)) →
          ∃! t, t ∈ T ∧ Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ))) →
        ∑ t ∈ T, χ (-(a * t)) * f t = 0) :
    ∀ x y : p.adicCompletion ℚ, f x = f y := by
  classical
  intro x y
  by_contra hne
  obtain ⟨ρ, hfρ⟩ := hf
  obtain ⟨γ₀, hγ₀⟩ := hχ₁
  have hχ0 : χ 0 = 1 := hγ₀ 0 (by simp)
  obtain ⟨g, hg, w, hw0, hwg, hw1⟩ := exists_conductor p χ γ₀ hγ₀ hχ₂
  have hcore := char_mul_eq_one_iff_of_conductor p χ hχ0 hg hw0 hwg hw1

  set rρ : ℤ := WithZero.log (ρ : WithZero (Multiplicative ℤ)) with hrρ
  have hρe : WithZero.exp rρ = (ρ : WithZero (Multiplicative ℤ)) := WithZero.exp_log ρ.ne_zero
  obtain ⟨βx, hβx⟩ := exists_unit_gt p x
  obtain ⟨βy, hβy⟩ := exists_unit_gt p y
  set lx : ℤ := WithZero.log (βx : WithZero (Multiplicative ℤ)) with hlx
  set ly : ℤ := WithZero.log (βy : WithZero (Multiplicative ℤ)) with hly
  have hxe : WithZero.exp lx = (βx : WithZero (Multiplicative ℤ)) := WithZero.exp_log βx.ne_zero
  have hye : WithZero.exp ly = (βy : WithZero (Multiplicative ℤ)) := WithZero.exp_log βy.ne_zero
  set e₀ : ℤ := max rρ (max lx ly) with he₀

  obtain ⟨win, hwin⟩ : ∃ win : ℕ → (WithZero (Multiplicative ℤ))ˣ,
      ∀ n : ℕ, ((win n : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) = WithZero.exp (e₀ + n) :=
    ⟨fun n => WithZero.expEquiv (e₀ + n), fun n => WithZero.coe_expEquiv_apply _⟩
  obtain ⟨ann, hann⟩ : ∃ ann : ℕ → (WithZero (Multiplicative ℤ))ˣ, ∀ n : ℕ,
      ((ann n : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) = WithZero.exp (g - (e₀ + n) + 1) :=
    ⟨fun n => WithZero.expEquiv (g - (e₀ + n) + 1), fun n => WithZero.coe_expEquiv_apply _⟩
  obtain ⟨R, hR⟩ : ∃ R : (WithZero (Multiplicative ℤ))ˣ,
      ((R : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) = WithZero.exp (g - rρ + 1) :=
    ⟨WithZero.expEquiv (g - rρ + 1), WithZero.coe_expEquiv_apply _⟩
  have hρwin : ∀ n : ℕ, ρ ≤ win n := fun n =>
    Units.val_le_val.mp (by rw [hwin, ← hρe]; exact WithZero.exp_le_exp.mpr (by omega))
  have hwin_mono : ∀ n : ℕ, win n ≤ win (n + 1) := fun n =>
    Units.val_le_val.mp (by rw [hwin, hwin]; exact WithZero.exp_le_exp.mpr (by push_cast; omega))
  have hann_anti : ∀ n : ℕ, ann (n + 1) ≤ ann n := fun n =>
    Units.val_le_val.mp (by rw [hann, hann]; exact WithZero.exp_le_exp.mpr (by push_cast; omega))
  have hann_le : ∀ n m : ℕ, n ≤ m →
      ((ann m : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) ≤ ann n := by
    intro n m hnm
    rw [hann, hann]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hann0R : ann 0 ≤ R :=
    Units.val_le_val.mp (by rw [hann, hR]; exact WithZero.exp_le_exp.mpr (by push_cast; omega))
  have hxwin : Valued.v x < ((win 0 : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) :=
    hβx.trans_le (by rw [hwin, ← hxe]; exact WithZero.exp_le_exp.mpr (by push_cast; omega))
  have hywin : Valued.v y < ((win 0 : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) :=
    hβy.trans_le (by rw [hwin, ← hye]; exact WithZero.exp_le_exp.mpr (by push_cast; omega))

  have hkills : ∀ (n : ℕ) (c : p.adicCompletion ℚ),
      (∀ z : p.adicCompletion ℚ, Valued.v z < (win n : WithZero (Multiplicative ℤ)) → χ (c * z) = 1) ↔
        Valued.v c < (ann n : WithZero (Multiplicative ℤ)) := by
    intro n c
    rw [hwin, hann]
    exact hcore (e₀ + n) c
  have hdual : ∀ (n : ℕ) (c : p.adicCompletion ℚ),
      (∀ z : p.adicCompletion ℚ, Valued.v z < (ann n : WithZero (Multiplicative ℤ)) → χ (c * z) = 1) ↔
        Valued.v c < (win n : WithZero (Multiplicative ℤ)) := by
    intro n c
    rw [hwin, hann]
    have h := hcore (g - (e₀ + n) + 1) c
    rwa [show g - (g - (e₀ + n) + 1) + 1 = e₀ + n by ring] at h
  have hr₀ : ∀ u : p.adicCompletion ℚ,
      (∀ z : p.adicCompletion ℚ, Valued.v z < (R : WithZero (Multiplicative ℤ)) → χ (u * z) = 1) ↔
        Valued.v u < (ρ : WithZero (Multiplicative ℤ)) := by
    intro u
    rw [hR, ← hρe]
    have h := hcore (g - rρ + 1) u
    rwa [show g - (g - rρ + 1) + 1 = rρ by ring] at h
  have hρkill : ∀ u : p.adicCompletion ℚ,
      (∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (u * z) = 1) ↔
        Valued.v u < (R : WithZero (Multiplicative ℤ)) := by
    intro u
    rw [hR, ← hρe]
    exact hcore rρ u
  have hs : ∀ u : p.adicCompletion ℚ, Valued.v u < (win 0 : WithZero (Multiplicative ℤ)) →
      ∀ z : p.adicCompletion ℚ, Valued.v z < (ann 0 : WithZero (Multiplicative ℤ)) → χ (u * z) = 1 :=
    fun u hu => (hdual 0 u).mpr hu

  choose Tsys hTsys using fun n : ℕ => exists_isRepSystem p (win n) ρ (hρwin n)
  choose Ksys hKsys using fun n : ℕ => exists_isRepSystem p (ann n) (ann (n + 1)) (hann_anti n)
  obtain ⟨Y, hY⟩ := exists_isRepSystem p R (ann 0) hann0R

  obtain ⟨Fw, hFw⟩ : ∃ Fw : ℕ → p.adicCompletion ℚ → ℂ,
      ∀ (n : ℕ) (a : p.adicCompletion ℚ), Fw n a = ∑ t ∈ Tsys n, χ (-(a * t)) * f t :=
    ⟨fun n a => ∑ t ∈ Tsys n, χ (-(a * t)) * f t, fun _ _ => rfl⟩

  obtain ⟨a₁, ha₁Y, hFa₁, hnk⟩ := exists_sum_twisted_ne_zero p χ hχ f hr₀ hs hY (hTsys 0) hfρ hxwin hywin hne
  have ha₁k : ∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (a₁ * z) = 1 :=
    (hρkill a₁).mpr (hY.1 a₁ ha₁Y)
  have hFa₁' : Fw 0 a₁ ≠ 0 := by rw [hFw]; exact hFa₁

  have hstep : ∀ (n : ℕ) (a : p.adicCompletion ℚ),
      (∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (a * z) = 1) ∧ Fw n a ≠ 0 →
      ∃ k : p.adicCompletion ℚ, Valued.v k < (ann n : WithZero (Multiplicative ℤ)) ∧
        ((∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ ((a + k) * z) = 1) ∧
          Fw (n + 1) (a + k) ≠ 0) := by
    rintro n a ⟨hak, hFa⟩
    have hsumK : ∑ k ∈ Ksys n, Fw (n + 1) (a + k) = ((Ksys n).card : ℂ) * Fw n a := by
      simp only [hFw]
      exact sum_sum_twisted_eq_count_mul p χ hχ f (hρwin n) (hwin_mono n) (hdual n) (hdual (n + 1)) (hKsys n)
        (hTsys n) (hTsys (n + 1)) a (twisted_const p χ hχ f hfρ hak)
    have hcard : (((Ksys n).card : ℕ) : ℂ) ≠ 0 := by
      obtain ⟨k, ⟨hk, -⟩, -⟩ := (hKsys n).2 0 (by simp)
      exact_mod_cast (Finset.card_pos.mpr ⟨k, hk⟩).ne'
    have hne' : ∑ k ∈ Ksys n, Fw (n + 1) (a + k) ≠ 0 := by
      rw [hsumK]
      exact mul_ne_zero hcard hFa
    obtain ⟨k, hkK, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    have hkann := (hKsys n).1 k hkK
    refine ⟨k, hkann, ?_, hk⟩
    intro z hz
    have hkw := (hkills n k).mpr hkann
    rw [add_mul, hχ, hak z hz, hkw z (hz.trans_le (Units.val_le_val.mpr (hρwin n))), mul_one]
  choose kf hkf using hstep

  let seq : (n : ℕ) → {a : p.adicCompletion ℚ //
      (∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (a * z) = 1) ∧ Fw n a ≠ 0} :=
    fun n => Nat.rec (motive := fun n => {a : p.adicCompletion ℚ //
        (∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (a * z) = 1) ∧ Fw n a ≠ 0})
      ⟨a₁, ha₁k, hFa₁'⟩ (fun m prev => ⟨prev.1 + kf m prev.1 prev.2, (hkf m prev.1 prev.2).2⟩) n
  have hseq_zero : (seq 0).1 = a₁ := rfl
  have hstep_close : ∀ n : ℕ,
      Valued.v ((seq (n + 1)).1 - (seq n).1) < (ann n : WithZero (Multiplicative ℤ)) := by
    intro n
    have e : (seq (n + 1)).1 - (seq n).1 = kf n (seq n).1 (seq n).2 := by
      show (seq n).1 + kf n (seq n).1 (seq n).2 - (seq n).1 = _
      ring
    rw [e]
    exact (hkf n (seq n).1 (seq n).2).1
  have hcoh : ∀ n j : ℕ, Valued.v ((seq (n + j)).1 - (seq n).1) < (ann n : WithZero (Multiplicative ℤ)) := by
    intro n j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (seq (n + (j + 1))).1 - (seq n).1
          = ((seq (n + j + 1)).1 - (seq (n + j)).1) + ((seq (n + j)).1 - (seq n).1) := by
        rw [← add_assoc]
        ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans_lt
        (max_lt ((hstep_close (n + j)).trans_le (hann_le n (n + j) (Nat.le_add_right n j))) ih)

  obtain ⟨Bu, hBu⟩ := exists_unit_gt p (seq 0).1
  set lB : ℤ := WithZero.log (Bu : WithZero (Multiplicative ℤ)) with hlB
  have hBe : WithZero.exp lB = (Bu : WithZero (Multiplicative ℤ)) := WithZero.exp_log Bu.ne_zero
  obtain ⟨Bd, hBd⟩ : ∃ Bd : (WithZero (Multiplicative ℤ))ˣ,
      ((Bd : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) = WithZero.exp (max lB (g - e₀ + 1)) :=
    ⟨WithZero.expEquiv _, WithZero.coe_expEquiv_apply _⟩
  have hBd₁ : (Bu : WithZero (Multiplicative ℤ)) ≤ Bd := by
    rw [hBd, ← hBe]
    exact WithZero.exp_le_exp.mpr (le_max_left _ _)
  have hBd₂ : ((ann 0 : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) ≤ Bd := by
    rw [hBd, hann]
    exact WithZero.exp_le_exp.mpr (by push_cast; omega)
  obtain ⟨K, hKc, hKmem⟩ := exists_isCompact_of_radius p Bd
  have hmemK : ∀ n : ℕ, (seq n).1 ∈ K := by
    intro n
    apply hKmem
    have h0 := hcoh 0 n
    rw [Nat.zero_add] at h0
    have e : Valued.v (seq n).1 = Valued.v ((seq 0).1 + ((seq n).1 - (seq 0).1)) := by
      congr 1
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (hBu.trans_le hBd₁) (h0.trans_le hBd₂))
  obtain ⟨a', -, hcl⟩ := hKc.exists_clusterPt (f := Filter.map (fun n => (seq n).1) Filter.atTop)
    (by
      rw [Filter.le_principal_iff, Filter.mem_map]
      exact Filter.univ_mem' hmemK)
  have hclose : ∀ n : ℕ, Valued.v (a' - (seq n).1) < (ann n : WithZero (Multiplicative ℤ)) := by
    intro n
    have hfreq := hcl.frequently (p := fun z => Valued.v (z - a') < (ann n : WithZero (Multiplicative ℤ)))
      (radiusBall_mem_nhds p a' (ann n))
    rw [Filter.frequently_map] at hfreq
    obtain ⟨m, hnm, hm⟩ := Filter.frequently_atTop.mp hfreq n
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have e : a' - (seq n).1 = -((seq (n + j)).1 - a') + ((seq (n + j)).1 - (seq n).1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ (hcoh n j))
    rw [Valuation.map_neg]
    exact hm

  have ha'k : ∀ z : p.adicCompletion ℚ, Valued.v z < (ρ : WithZero (Multiplicative ℤ)) → χ (a' * z) = 1 := by
    intro z hz
    have e : a' * z = (seq 0).1 * z + (a' - (seq 0).1) * z := by ring
    rw [e, hχ, (seq 0).2.1 z hz, (hkills 0 _).mpr (hclose 0) z (hz.trans_le (Units.val_le_val.mpr (hρwin 0))),
      mul_one]
  have ha'0 : a' ≠ 0 := by
    intro h0
    have h := hclose 0
    rw [h0, zero_sub, Valuation.map_neg, hseq_zero] at h
    exact hnk ((hkills 0 a₁).mpr h)
  have hlive : ∀ n : ℕ, Fw n a' ≠ 0 := by
    intro n
    have h := (seq n).2.2
    rw [hFw] at h ⊢
    have hk := (hkills n _).mpr (hclose n)
    have e : a' = (seq n).1 + (a' - (seq n).1) := by ring
    rw [e, sum_twisted_add_eq p χ hχ f (hTsys n).1 (seq n).1 hk]
    exact h

  obtain ⟨β₀, hβ₀⟩ := hsum a' ha'0
  set lβ : ℤ := WithZero.log (β₀ : WithZero (Multiplicative ℤ)) with hlβ
  have hβe : WithZero.exp lβ = (β₀ : WithZero (Multiplicative ℤ)) := WithZero.exp_log β₀.ne_zero
  set n₀ : ℕ := (lβ - e₀).toNat with hn₀
  have hβ₀n : β₀ ≤ win n₀ := by
    refine Units.val_le_val.mp ?_
    rw [hwin, ← hβe]
    refine WithZero.exp_le_exp.mpr ?_
    have := Int.self_le_toNat (lβ - e₀)
    omega
  obtain ⟨δ', hδ'⟩ := hβ₀ (win n₀) hβ₀n
  have hvan : ∀ T : Finset (p.adicCompletion ℚ), IsRepSystem p (win n₀) δ' T →
      ∑ t ∈ T, χ (-(a' * t)) * f t = 0 :=
    fun T hT => hδ' T hT.1 hT.2
  have hzero := sum_eq_zero_of_forall_isRepSystem p (hρwin n₀) δ' (fun t => χ (-(a' * t)) * f t)
    (twisted_const p χ hχ f hfρ ha'k) hvan (hTsys n₀)
  have h := hlive n₀
  rw [hFw] at h
  exact h hzero

end S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero (solution)
