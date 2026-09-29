-- Prove2me | solution 1 for AutomorphicForm.LocalFunctionSpace.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3edb4087-4b2f-57f2-a028-9a3cbdf5d061

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Mathlib.NumberTheory.Padics.ProperSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span

set_option autoImplicit false

open AutomorphicForm IsDedekindDomain

open scoped Classical

namespace KirillovBumpAux

variable (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
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

private theorem exists_unit_gt (y : F) : ∃ β₀ : Γ, Valued.v y < (β₀ : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨1, by simp⟩
  · have hv : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hy
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hv
    refine ⟨Units.mk0 ((m * Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      WithZero.coe_ne_zero, ?_⟩
    rw [← hm, Units.val_mk0, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_ofAdd]
    exact lt_add_one _

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

private theorem exists_psiV_eq_one :
    ∃ γ₀ : Γ, ∀ x : F, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) →
      NumberField.StandardAddChar.psiV p x = 1 := by
  refine ⟨1, fun x hx => NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using hx.le

private theorem continuous_unipotentGL2 : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

private theorem exists_unipotent_mem_of_isOpen (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ δ : Γ, ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) → unipotentGL2 z ∈ K := by
  have hU : ((fun z : F => (unipotentGL2 z : G)) ⁻¹' (K : Set G)) ∈ nhds (0 : F) := by
    apply (hK.preimage (continuous_unipotentGL2 p)).mem_nhds
    show unipotentGL2 (0 : F) ∈ K
    rw [unipotentGL2_zero]
    exact K.one_mem
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation _).mp hU
  have hb : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ (0 : WithZero (Multiplicative ℤ)) := by
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ hb, fun z hz => ?_⟩
  apply hγ
  show Valued.v.restrict z < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa using hz

private theorem sum_char_eq_zero {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) (c : F)
    (hsmall : ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) →
      NumberField.StandardAddChar.psiV p (c * z) = 1)
    (hbig : ∃ y : F, Valued.v y < (β : WithZero (Multiplicative ℤ)) ∧
      NumberField.StandardAddChar.psiV p (c * y) ≠ 1) :
    ∑ x ∈ T, NumberField.StandardAddChar.psiV p (c * x) = 0 := by
  obtain ⟨y, hy, hy1⟩ := hbig
  have hconst : ∀ x x' : F, Valued.v (x - x') < (δ : WithZero (Multiplicative ℤ)) →
      NumberField.StandardAddChar.psiV p (c * x) = NumberField.StandardAddChar.psiV p (c * x') := by
    intro x x' hxx'
    have e : c * x = c * x' + c * (x - x') := by ring
    rw [e, AddChar.map_add_eq_mul, hsmall _ hxx', mul_one]
  have h1 : ∑ x ∈ T, NumberField.StandardAddChar.psiV p (c * x)
      = ∑ x ∈ T.image (· + y), NumberField.StandardAddChar.psiV p (c * x) :=
    sum_eq_sum_of_isRepSystem p hT (isRepSystem_image_add p hT hy) _ hconst
  have h2 : ∑ x ∈ T.image (· + y), NumberField.StandardAddChar.psiV p (c * x)
      = NumberField.StandardAddChar.psiV p (c * y) * ∑ x ∈ T, NumberField.StandardAddChar.psiV p (c * x) := by
    rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_add, AddChar.map_add_eq_mul, mul_comm]
  have h3 : (NumberField.StandardAddChar.psiV p (c * y) - 1) *
      ∑ x ∈ T, NumberField.StandardAddChar.psiV p (c * x) = 0 := by
    rw [sub_mul, one_mul, ← h2, ← h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) hy1
  · exact h

private theorem diagonal_mul_unipotent (t : G) (h01 : (t : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h11 : (t : Matrix (Fin 2) (Fin 2) F) 1 1 = 1) (x : F) :
    t * unipotentGL2 x = unipotentGL2 ((t : Matrix (Fin 2) (Fin 2) F) 0 0 * x) * t := by
  apply Units.ext
  simp only [Units.val_mul, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h11]

private theorem unipotent_mul_comm (x z : F) : unipotentGL2 x * unipotentGL2 z = unipotentGL2 z * unipotentGL2 x := by
  rw [← unipotentGL2_add, ← unipotentGL2_add, add_comm]

end KirillovBumpAux

open KirillovBumpAux in

theorem solution
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ U ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => U (g * k)) ∈ S)
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (a₀ : p.adicCompletion ℚ) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ W' ∈ S, ∀ t : GL (Fin 2) (p.adicCompletion ℚ),
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 →
      (Valued.v ((t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) ∧
      (¬ Valued.v ((t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) := by
  classical

  obtain ⟨K, hKopen, hKfix⟩ := hsmW
  obtain ⟨δW, hδW⟩ := exists_unipotent_mem_of_isOpen p K hKopen
  obtain ⟨γ₀, hγ₀⟩ := exists_psiV_eq_one p
  have hψadd : ∀ x y : p.adicCompletion ℚ, NumberField.StandardAddChar.psiV p (x + y)
      = NumberField.StandardAddChar.psiV p x * NumberField.StandardAddChar.psiV p y :=
    fun x y => AddChar.map_add_eq_mul _ x y
  have hψnt : ∃ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiV p x ≠ 1 :=
    ⟨_, NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p⟩
  obtain ⟨r₀, hr₀⟩ := exists_forall_char_mul_eq_one_iff p (NumberField.StandardAddChar.psiV p) γ₀ hγ₀ hψnt δ
  obtain ⟨βa, hβa⟩ := exists_unit_gt p (-a₀)
  obtain ⟨ra, hra⟩ := exists_forall_char_mul_eq_one_iff p (NumberField.StandardAddChar.psiV p) γ₀ hγ₀ hψnt βa
  have hra' : ∀ z : p.adicCompletion ℚ, Valued.v z < (ra : WithZero (Multiplicative ℤ)) →
      NumberField.StandardAddChar.psiV p (-a₀ * z) = 1 := (hra (-a₀)).mpr hβa
  set r₁ : (WithZero (Multiplicative ℤ))ˣ := min (min δW ra) r₀ with hr₁
  have hr₁W : ∀ z : p.adicCompletion ℚ, Valued.v z < (r₁ : WithZero (Multiplicative ℤ)) →
      AutomorphicForm.unipotentGL2 z ∈ K := fun z hz =>
    hδW z (hz.trans_le (Units.val_le_val.mpr ((min_le_left _ _).trans (min_le_left _ _))))
  have hr₁a : ∀ z : p.adicCompletion ℚ, Valued.v z < (r₁ : WithZero (Multiplicative ℤ)) →
      NumberField.StandardAddChar.psiV p (-a₀ * z) = 1 := fun z hz =>
    hra' z (hz.trans_le (Units.val_le_val.mpr ((min_le_left _ _).trans (min_le_right _ _))))
  obtain ⟨T, hT⟩ := exists_isRepSystem p r₀ r₁ (min_le_right _ _)

  have hT0 : T.Nonempty := by
    obtain ⟨t, ⟨ht, -⟩, -⟩ := hT.2 0 (by simp)
    exact ⟨t, ht⟩
  set m : ℂ := (T.card : ℂ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact_mod_cast (Finset.card_pos.mpr hT0).ne'
  set W' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := m⁻¹ • ∑ x ∈ T,
    NumberField.StandardAddChar.psiV p (-a₀ * x) • (fun g => W (g * AutomorphicForm.unipotentGL2 x)) with hW'
  have hW'S : W' ∈ S := by
    rw [hW']
    exact S.smul_mem _ (S.sum_mem fun x _ => S.smul_mem _ (hstab W hW _))

  have hW'fix : ∀ z : p.adicCompletion ℚ, Valued.v z < (r₁ : WithZero (Multiplicative ℤ)) →
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W' (h * AutomorphicForm.unipotentGL2 z) = W' h := by
    intro z hz h
    simp only [hW', Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [mul_assoc, unipotent_mul_comm, ← mul_assoc]
    exact congrFun (hKfix _ (hr₁W z hz)) (h * AutomorphicForm.unipotentGL2 x)
  refine ⟨W', hW'S, fun t h01 h10 h11 => ?_⟩
  set a : p.adicCompletion ℚ := (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 with ha
  have hcomm : ∀ x : p.adicCompletion ℚ, t * AutomorphicForm.unipotentGL2 x
      = AutomorphicForm.unipotentGL2 (a * x) * t := diagonal_mul_unipotent p t h01 h10 h11
  set U : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => W (g * t) with hU
  have hUS : U ∈ S := by
    rw [hU]
    exact hstab W hW t

  set σ : ℂ := m⁻¹ * ∑ x ∈ T,
    NumberField.StandardAddChar.psiV p (-a₀ * x) * NumberField.StandardAddChar.psiV p (a * x) with hσ
  set D : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) := Submodule.span ℂ
    {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
      V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U} with hD
  have hgen : ∀ x : p.adicCompletion ℚ,
      (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U ∈ D := by
    intro x
    rw [hD]
    exact Submodule.subset_span ⟨U, hUS, x, rfl⟩
  have htrans : (fun g => W' (g * t)) = m⁻¹ • ∑ x ∈ T, NumberField.StandardAddChar.psiV p (-a₀ * x) •
      (fun g => U (g * AutomorphicForm.unipotentGL2 (a * x))) := by
    funext g
    simp only [hW', hU, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [mul_assoc, hcomm, ← mul_assoc]
  have hkey : (fun g => W' (g * t)) - σ • U ∈ D := by
    have hsum : ∑ x ∈ T, NumberField.StandardAddChar.psiV p (-a₀ * x) •
          (fun g => U (g * AutomorphicForm.unipotentGL2 (a * x)))
        = ∑ x ∈ T, NumberField.StandardAddChar.psiV p (-a₀ * x) •
            ((fun g => U (g * AutomorphicForm.unipotentGL2 (a * x)))
              - NumberField.StandardAddChar.psiV p (a * x) • U)
          + ∑ x ∈ T, (NumberField.StandardAddChar.psiV p (-a₀ * x) *
              NumberField.StandardAddChar.psiV p (a * x)) • U := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_smul, ← smul_add, sub_add_cancel]
    have hrest : (fun g => W' (g * t)) - σ • U = m⁻¹ • ∑ x ∈ T, NumberField.StandardAddChar.psiV p (-a₀ * x) •
        ((fun g => U (g * AutomorphicForm.unipotentGL2 (a * x)))
          - NumberField.StandardAddChar.psiV p (a * x) • U) := by
      rw [htrans, hsum, ← Finset.sum_smul, smul_add, hσ, mul_smul, add_sub_cancel_right]
    rw [hrest]
    exact D.smul_mem _ (D.sum_mem fun x _ => D.smul_mem _ (hgen (a * x)))
  have hprod : ∀ x : p.adicCompletion ℚ,
      NumberField.StandardAddChar.psiV p (-a₀ * x) * NumberField.StandardAddChar.psiV p (a * x)
        = NumberField.StandardAddChar.psiV p ((a - a₀) * x) := by
    intro x
    rw [← hψadd]
    congr 1
    ring
  refine ⟨fun hlt => ?_, fun hnlt => ?_⟩
  ·
    have hσ1 : σ = 1 := by
      rw [hσ, Finset.sum_congr rfl (fun x hx => (hprod x).trans
        ((hr₀ (a - a₀)).mpr hlt x (hT.1 x hx))), Finset.sum_const, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hm0
    have := hkey
    rw [hσ1, one_smul] at this
    exact this
  ·
    by_cases hann : ∀ z : p.adicCompletion ℚ, Valued.v z < (r₁ : WithZero (Multiplicative ℤ)) →
        NumberField.StandardAddChar.psiV p (a * z) = 1
    · have hσ0 : σ = 0 := by
        have hsmall : ∀ z : p.adicCompletion ℚ, Valued.v z < (r₁ : WithZero (Multiplicative ℤ)) →
            NumberField.StandardAddChar.psiV p ((a - a₀) * z) = 1 := by
          intro z hz
          rw [← hprod, hr₁a z hz, hann z hz, mul_one]
        have hbig : ∃ y : p.adicCompletion ℚ, Valued.v y < (r₀ : WithZero (Multiplicative ℤ)) ∧
            NumberField.StandardAddChar.psiV p ((a - a₀) * y) ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hnlt ((hr₀ (a - a₀)).mp hcon)
        rw [hσ, Finset.sum_congr rfl (fun x _ => hprod x), sum_char_eq_zero p hT (a - a₀) hsmall hbig, mul_zero]
      have := hkey
      rw [hσ0, zero_smul, sub_zero] at this
      exact this
    · push Not at hann
      obtain ⟨z, hz, hz1⟩ := hann
      set U' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => W' (g * t) with hU'
      have hU'S : U' ∈ S := by
        rw [hU']
        exact hstab W' hW'S t
      have hU'fix : (fun g => U' (g * AutomorphicForm.unipotentGL2 (a * z))) = U' := by
        funext g
        simp only [hU']
        rw [mul_assoc, ← hcomm, ← mul_assoc]
        exact hW'fix z hz (g * t)
      have hgen' : (fun g => U' (g * AutomorphicForm.unipotentGL2 (a * z)))
          - NumberField.StandardAddChar.psiV p (a * z) • U' ∈ D := by
        rw [hD]
        exact Submodule.subset_span ⟨U', hU'S, a * z, rfl⟩
      rw [hU'fix] at hgen'
      have hne : (1 : ℂ) - NumberField.StandardAddChar.psiV p (a * z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
      have hform : U' - NumberField.StandardAddChar.psiV p (a * z) • U'
          = (1 - NumberField.StandardAddChar.psiV p (a * z)) • U' := by
        rw [sub_smul, one_smul]
      rw [hform] at hgen'
      have hmem := D.smul_mem (1 - NumberField.StandardAddChar.psiV p (a * z))⁻¹ hgen'
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at hmem
      exact hmem

end S_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
end P2MW
export P2MW.S_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span (solution)
