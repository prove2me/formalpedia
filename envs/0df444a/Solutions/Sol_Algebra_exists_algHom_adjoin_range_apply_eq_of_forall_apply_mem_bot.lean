-- Prove2me | solution 1 for Algebra.exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a9257e4c-37e8-5494-b84d-604cf7603724

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open scoped BigOperators

namespace LinDisjAux

variable {κ : Type*} [Field κ]

theorem exists_int_of_mem_bot {x : κ} (hx : x ∈ (⊥ : Subfield κ)) :
    ∃ m d : ℤ, (d : κ) ≠ 0 ∧ x * (d : κ) = (m : κ) := by
  rw [← Subfield.closure_empty, Subfield.mem_closure_iff] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := hx
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨d, rfl⟩ := hz
  by_cases hd : ((d : ℤ) : κ) = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← hyz, hd, div_zero]; simp
  · refine ⟨m, d, hd, ?_⟩
    rw [← hyz, div_mul_cancel₀ _ hd]

section Systems

variable (F : Subfield κ) {σ : Type*} {ι : Type*} [DecidableEq σ]

def Sol (s : Finset σ) (v : σ → ι → κ) : Set (σ → κ) :=
  {b | (∀ k, b k ∈ F) ∧ (∀ k, k ∉ s → b k = 0) ∧ ∀ n, ∑ k ∈ s, b k * v k n = 0}

omit [DecidableEq σ] in
theorem mem_Sol_iff {s : Finset σ} {v : σ → ι → κ} {b : σ → κ} :
    b ∈ Sol F s v ↔ (∀ k, b k ∈ F) ∧ (∀ k, k ∉ s → b k = 0) ∧ ∀ n, ∑ k ∈ s, b k * v k n = 0 :=
  Iff.rfl

theorem mem_span_Sol (s : Finset σ) :
    ∀ (v : σ → ι → κ) (_ : ∀ k n, v k n ∈ F) (a : σ → κ) (_ : ∀ k, k ∉ s → a k = 0)
      (_ : ∀ n, ∑ k ∈ s, a k * v k n = 0), a ∈ Submodule.span κ (Sol F s v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv a ha0 ha
    have : a = 0 := funext fun k => ha0 k (by simp)
    rw [this]; exact Submodule.zero_mem _
  | @insert i₀ s hi₀ IH =>
    intro v hv a ha0 ha

    set a' : σ → κ := Function.update a i₀ 0 with ha'def
    have ha'i₀ : a' i₀ = 0 := by rw [ha'def, Function.update_self]
    have ha'ne : ∀ k, k ≠ i₀ → a' k = a k := fun k hk => by rw [ha'def, Function.update_of_ne hk]
    have ha0' : ∀ k, k ∉ s → a' k = 0 := by
      intro k hk
      by_cases hki : k = i₀
      · rw [hki]; exact ha'i₀
      · rw [ha'ne k hki]; exact ha0 k (by simp [hki, hk])
    have hsum_a' : ∀ w : σ → κ, ∑ k ∈ s, a' k * w k = ∑ k ∈ s, a k * w k := by
      intro w
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ha'ne k (fun h => hi₀ (by rw [← h]; exact hk))]

    have hsplit : ∀ n, ∑ k ∈ s, a k * v k n = -(a i₀ * v i₀ n) := by
      intro n
      have h := ha n
      rw [Finset.sum_insert hi₀] at h
      linear_combination h
    by_cases hzero : ∀ n, v i₀ n = 0
    ·
      have ha' : ∀ n, ∑ k ∈ s, a' k * v k n = 0 := by
        intro n; rw [hsum_a', hsplit, hzero n, mul_zero, neg_zero]
      have hIH := IH v hv a' ha0' ha'
      have hsub : Sol F s v ⊆ Sol F (insert i₀ s) v := by
        intro b hb
        obtain ⟨hbF, hb0, hbrel⟩ := hb
        refine ⟨hbF, fun k hk => hb0 k (fun h => hk (Finset.mem_insert_of_mem h)), fun n => ?_⟩
        rw [Finset.sum_insert hi₀, hbrel n, hb0 i₀ hi₀, zero_mul, zero_add]
      have he : (Pi.single i₀ (1 : κ) : σ → κ) ∈ Sol F (insert i₀ s) v := by
        refine ⟨fun k => ?_, fun k hk => ?_, fun n => ?_⟩
        · by_cases hk : k = i₀
          · subst hk; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
        · have hk' : k ≠ i₀ := fun h => hk (by simp [h])
          rw [Pi.single_eq_of_ne hk']
        · rw [Finset.sum_insert hi₀, Pi.single_eq_same, one_mul, hzero n, zero_add]
          refine Finset.sum_eq_zero fun k hk => ?_
          rw [Pi.single_eq_of_ne (fun h => hi₀ (by rw [← h]; exact hk)), zero_mul]
      have hdecomp : a = a' + a i₀ • (Pi.single i₀ (1 : κ) : σ → κ) := by
        funext k
        by_cases hk : k = i₀
        · subst hk
          rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, ha'i₀, smul_eq_mul, mul_one, zero_add]
        · rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, add_zero, ha'ne k hk]
      rw [hdecomp]
      exact Submodule.add_mem _ (Submodule.span_mono hsub hIH)
        (Submodule.smul_mem _ _ (Submodule.subset_span he))
    ·
      push Not at hzero
      obtain ⟨n₀, hn₀⟩ := hzero
      have hwF : v i₀ n₀ ∈ F := hv i₀ n₀

      set v' : σ → ι → κ := fun k n => v k n - v k n₀ / v i₀ n₀ * v i₀ n with hv'def
      have hv' : ∀ k n, v' k n ∈ F := fun k n =>
        sub_mem (hv k n) (mul_mem (div_mem (hv k n₀) hwF) (hv i₀ n))
      have ha' : ∀ n, ∑ k ∈ s, a' k * v' k n = 0 := by
        intro n
        have h1 : ∑ k ∈ s, a' k * v' k n = ∑ k ∈ s, a k * v k n - (∑ k ∈ s, a k * v k n₀) / v i₀ n₀ * v i₀ n := by
          rw [hsum_a', Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hv'def]; ring
        rw [h1, hsplit, hsplit n₀]
        field_simp
        ring
      have hIH := IH v' hv' a' ha0' ha'

      let E : (σ → κ) →ₗ[κ] (σ → κ) :=
        { toFun := fun b => b + (-(∑ k ∈ s, b k * v k n₀) / v i₀ n₀) • (Pi.single i₀ (1 : κ) : σ → κ)
          map_add' := fun b₁ b₂ => by
            funext k
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [show ∑ k ∈ s, (b₁ k + b₂ k) * v k n₀ = ∑ k ∈ s, b₁ k * v k n₀ + ∑ k ∈ s, b₂ k * v k n₀ from by
              rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => add_mul _ _ _]
            ring
          map_smul' := fun r b => by
            funext k
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            rw [show ∑ k ∈ s, r * b k * v k n₀ = r * ∑ k ∈ s, b k * v k n₀ from by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _]
            ring }
      have hE_apply : ∀ b : σ → κ, E b = b + (-(∑ k ∈ s, b k * v k n₀) / v i₀ n₀) • (Pi.single i₀ (1 : κ) : σ → κ) :=
        fun b => rfl

      have hEa : E a' = a := by
        rw [hE_apply]
        funext k
        by_cases hk : k = i₀
        · subst hk
          rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ha'i₀, zero_add, hsum_a',
            hsplit n₀]
          field_simp
        · rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, add_zero, ha'ne k hk]

      have hEsol : ∀ b ∈ Sol F s v', E b ∈ Sol F (insert i₀ s) v := by
        intro b hb
        obtain ⟨hbF, hb0, hbrel⟩ := hb
        have hcF : (-(∑ k ∈ s, b k * v k n₀) / v i₀ n₀) ∈ F :=
          div_mem (neg_mem (sum_mem fun k _ => mul_mem (hbF k) (hv k n₀))) hwF
        rw [hE_apply]
        refine ⟨fun k => ?_, fun k hk => ?_, fun n => ?_⟩
        · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          by_cases hk : k = i₀
          · subst hk; rw [Pi.single_eq_same, mul_one]; exact add_mem (hbF _) hcF
          · rw [Pi.single_eq_of_ne hk, mul_zero, add_zero]; exact hbF k
        · have hk' : k ≠ i₀ := fun h => hk (by simp [h])
          have hks : k ∉ s := fun h => hk (Finset.mem_insert_of_mem h)
          rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hk', smul_zero, add_zero, hb0 k hks]
        · rw [Finset.sum_insert hi₀]
          have hin : ∀ k ∈ s, (b + (-(∑ k ∈ s, b k * v k n₀) / v i₀ n₀) • (Pi.single i₀ (1 : κ) : σ → κ)) k * v k n =
              b k * v k n := by
            intro k hk
            rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hi₀ (by rw [← h]; exact hk)), smul_zero, add_zero]
          rw [Finset.sum_congr rfl hin, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
            hb0 i₀ hi₀, zero_add]

          have hrel : ∑ k ∈ s, b k * v k n = (∑ k ∈ s, b k * v k n₀) / v i₀ n₀ * v i₀ n := by
            have h := hbrel n
            have h1 : ∑ k ∈ s, b k * v' k n = ∑ k ∈ s, b k * v k n - (∑ k ∈ s, b k * v k n₀) / v i₀ n₀ * v i₀ n := by
              rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hv'def]; ring
            rw [h1] at h
            linear_combination h
          rw [hrel]; ring

      rw [← hEa]
      have hmap : E a' ∈ Submodule.map E (Submodule.span κ (Sol F s v')) := Submodule.mem_map_of_mem hIH
      rw [Submodule.map_span] at hmap
      refine Submodule.span_mono ?_ hmap
      rintro _ ⟨b, hb, rfl⟩
      exact hEsol b hb

end Systems

section Main

variable {B : Type*} [Ring B] [Algebra κ B] {ι : Type*} (c : ι → (B →ₗ[κ] κ))
  {T : Type*} [CommRing T] (red : T →+* B) (ρ : T →+* κ)

theorem sum_mul_apply_eq_zero (hc : ∀ b : B, (∀ i, c i b = 0) → b = 0)
    (hbot : ∀ (t : T) (i : ι), c i (red t) ∈ (⊥ : Subfield κ))
    (hker : ∀ t : T, red t = 0 → ρ t = 0)
    (s : Finset T) (a : T → κ) (ha : ∑ t ∈ s, a t • red t = 0) : ∑ t ∈ s, a t * ρ t = 0 := by
  classical

  set v : T → ι → κ := fun t i => c i (red t) with hvdef
  have hv : ∀ t i, v t i ∈ (⊥ : Subfield κ) := fun t i => hbot t i

  set a₀ : T → κ := fun t => if t ∈ s then a t else 0 with ha₀def
  have ha₀s : ∀ t ∈ s, a₀ t = a t := fun t ht => by rw [ha₀def]; simp [ht]
  have ha₀0 : ∀ t, t ∉ s → a₀ t = 0 := fun t ht => by rw [ha₀def]; simp [ht]
  have hrel : ∀ i, ∑ t ∈ s, a₀ t * v t i = 0 := by
    intro i
    have h := congrArg (c i) ha
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [ha₀s t ht, map_smul, smul_eq_mul]
  have hspan := mem_span_Sol (⊥ : Subfield κ) s v hv a₀ ha₀0 hrel

  let Λ : (T → κ) →ₗ[κ] κ :=
    { toFun := fun b => ∑ t ∈ s, b t * ρ t
      map_add' := fun b₁ b₂ => by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun t _ => add_mul _ _ _
      map_smul' := fun r b => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc] }
  have hΛ_apply : ∀ b : T → κ, Λ b = ∑ t ∈ s, b t * ρ t := fun b => rfl
  have hΛsol : ∀ b ∈ Sol (⊥ : Subfield κ) s v, Λ b = 0 := by
    intro b hb
    obtain ⟨hbF, -, hbrel⟩ := hb

    have hmd : ∀ t, ∃ m d : ℤ, (d : κ) ≠ 0 ∧ b t * (d : κ) = (m : κ) := fun t => exists_int_of_mem_bot (hbF t)
    choose m d hd hmd using hmd
    set D : κ := ∏ t ∈ s, (d t : κ) with hDdef
    have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hd t

    set Z : T → ℤ := fun t => m t * ∏ t' ∈ s.erase t, d t' with hZdef
    have hZ : ∀ t ∈ s, (Z t : κ) = b t * D := by
      intro t ht
      rw [hZdef]
      simp only [Int.cast_mul, Int.cast_prod]
      rw [← hmd t, hDdef, ← Finset.mul_prod_erase s (fun t => (d t : κ)) ht]
      ring

    set x : T := ∑ t ∈ s, (Z t : T) * t with hxdef
    have hredx : red x = 0 := by
      apply hc
      intro i
      rw [hxdef, map_sum, map_sum]
      have h1 : ∀ t ∈ s, c i (red ((Z t : T) * t)) = D * (b t * v t i) := by
        intro t ht
        rw [map_mul, map_intCast, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul κ, map_smul, smul_eq_mul, hZ t ht]
        rw [hvdef]; ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hbrel i, mul_zero]
    have hρx : ρ x = 0 := hker x hredx
    rw [hxdef, map_sum] at hρx
    have h2 : ∀ t ∈ s, ρ ((Z t : T) * t) = D * (b t * ρ t) := by
      intro t ht
      rw [map_mul, map_intCast, hZ t ht]; ring
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum] at hρx
    rw [hΛ_apply]
    rcases mul_eq_zero.mp hρx with h | h
    · exact absurd h hD
    · exact h

  have hker_le : Submodule.span κ (Sol (⊥ : Subfield κ) s v) ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    intro b hb
    exact hΛsol b hb
  have h := hker_le hspan
  rw [LinearMap.mem_ker, hΛ_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun t ht => by rw [ha₀s t ht]

end Main

end LinDisjAux

end

open LinDisjAux

theorem solution
    {κ : Type*} [Field κ] {B : Type*} [Ring B] [Algebra κ B]
    {ι : Type*} (c : ι → (B →ₗ[κ] κ)) (hc : ∀ b : B, (∀ i, c i b = 0) → b = 0)
    {T : Type*} [CommRing T] (red : T →+* B) (ρ : T →+* κ)
    (hbot : ∀ (t : T) (i : ι), c i (red t) ∈ (⊥ : Subfield κ))
    (hker : ∀ t : T, red t = 0 → ρ t = 0) :
    ∃ χ : ↥(Algebra.adjoin κ (Set.range red)) →ₐ[κ] κ,
      ∀ t : T, χ ⟨red t, Algebra.subset_adjoin (Set.mem_range_self t)⟩ = ρ t := by
  classical

  have hrelation : ∀ l : T →₀ κ, (Finsupp.linearCombination κ (fun t => red t)) l = 0 →
      (Finsupp.linearCombination κ (fun t => ρ t)) l = 0 := by
    intro l hl
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl ⊢
    have h := sum_mul_apply_eq_zero c red ρ hc hbot hker l.support l hl
    simpa [smul_eq_mul] using h

  set Φ : (T →₀ κ) →ₗ[κ] B := Finsupp.linearCombination κ (fun t => red t) with hΦdef
  set Ψ : (T →₀ κ) →ₗ[κ] κ := Finsupp.linearCombination κ (fun t => ρ t) with hΨdef
  have hkerle : LinearMap.ker Φ ≤ LinearMap.ker Ψ := fun l hl => hrelation l hl
  let φ₀ : ↥(LinearMap.range Φ) →ₗ[κ] κ := ((LinearMap.ker Φ).liftQ Ψ hkerle).comp Φ.quotKerEquivRange.symm.toLinearMap
  have hφ₀ : ∀ (l : T →₀ κ) (h : Φ l ∈ LinearMap.range Φ), φ₀ ⟨Φ l, h⟩ = Ψ l := by
    intro l h
    change ((LinearMap.ker Φ).liftQ Ψ hkerle) (Φ.quotKerEquivRange.symm ⟨Φ l, h⟩) = Ψ l
    rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

  have hrange : LinearMap.range Φ = Submodule.span κ (Set.range red) := by
    rw [hΦdef, Finsupp.range_linearCombination]
  have hadj : Subalgebra.toSubmodule (Algebra.adjoin κ (Set.range red)) = Submodule.span κ (Set.range red) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range red = ((MonoidHom.mrange red.toMonoidHom : Submonoid B) : Set B) := by
      rw [MonoidHom.coe_mrange]; rfl
    rw [this, Submonoid.closure_eq]
  have hmem : ∀ {x : B}, x ∈ Algebra.adjoin κ (Set.range red) ↔ x ∈ LinearMap.range Φ := by
    intro x
    rw [hrange, ← hadj, Subalgebra.mem_toSubmodule]

  let χ' : B → κ := fun x => if h : x ∈ LinearMap.range Φ then φ₀ ⟨x, h⟩ else 0
  have hχ'_of : ∀ (x : B) (h : x ∈ LinearMap.range Φ), χ' x = φ₀ ⟨x, h⟩ := by
    intro x h; simp only [χ', dif_pos h]
  have hχ'Φ : ∀ l : T →₀ κ, χ' (Φ l) = Ψ l := by
    intro l
    rw [hχ'_of (Φ l) (LinearMap.mem_range_self Φ l), hφ₀]

  have hΦsingle : ∀ t : T, Φ (Finsupp.single t 1) = red t := by
    intro t; rw [hΦdef, Finsupp.linearCombination_single, one_smul]
  have hΨsingle : ∀ t : T, Ψ (Finsupp.single t 1) = ρ t := by
    intro t; rw [hΨdef, Finsupp.linearCombination_single, one_smul]
  have hχ'red : ∀ t : T, χ' (red t) = ρ t := by
    intro t; rw [← hΦsingle, hχ'Φ, hΨsingle]

  have hV : ∀ {x : B}, x ∈ LinearMap.range Φ → ∃ l : T →₀ κ, Φ l = x := fun hx => hx
  have hχ'add : ∀ x y : B, x ∈ LinearMap.range Φ → y ∈ LinearMap.range Φ → χ' (x + y) = χ' x + χ' y := by
    intro x y hx hy
    obtain ⟨l₁, rfl⟩ := hV hx
    obtain ⟨l₂, rfl⟩ := hV hy
    rw [← map_add, hχ'Φ, hχ'Φ, hχ'Φ, map_add]
  have hχ'smul : ∀ (r : κ) (x : B), x ∈ LinearMap.range Φ → χ' (r • x) = r * χ' x := by
    intro r x hx
    obtain ⟨l, rfl⟩ := hV hx
    rw [← map_smul, hχ'Φ, hχ'Φ, map_smul, smul_eq_mul]
  have hχ'zero : χ' 0 = 0 := by
    have := hχ'Φ 0
    rwa [map_zero, map_zero] at this

  have hmulmem : ∀ x y : B, x ∈ LinearMap.range Φ → y ∈ LinearMap.range Φ → x * y ∈ LinearMap.range Φ := by
    intro x y hx hy
    exact hmem.mp (Subalgebra.mul_mem _ (hmem.mpr hx) (hmem.mpr hy))
  have hχ'mul_gen : ∀ (t : T) (x : B), x ∈ LinearMap.range Φ → χ' (x * red t) = χ' x * ρ t := by
    intro t x hx
    rw [hrange] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      rw [← map_mul, hχ'red, hχ'red, map_mul]
    | zero => rw [zero_mul, hχ'zero, zero_mul]
    | add y z hy hz ihy ihz =>
      have hy' : y ∈ LinearMap.range Φ := by rw [hrange]; exact hy
      have hz' : z ∈ LinearMap.range Φ := by rw [hrange]; exact hz
      have hty : red t ∈ LinearMap.range Φ := by rw [hrange]; exact Submodule.subset_span (Set.mem_range_self t)
      rw [add_mul, hχ'add _ _ (hmulmem _ _ hy' hty) (hmulmem _ _ hz' hty), ihy, ihz, hχ'add _ _ hy' hz', add_mul]
    | smul r y hy ihy =>
      have hy' : y ∈ LinearMap.range Φ := by rw [hrange]; exact hy
      have hty : red t ∈ LinearMap.range Φ := by rw [hrange]; exact Submodule.subset_span (Set.mem_range_self t)
      rw [smul_mul_assoc, hχ'smul _ _ (hmulmem _ _ hy' hty), ihy, hχ'smul _ _ hy', mul_assoc]
  have hχ'mul : ∀ x y : B, x ∈ LinearMap.range Φ → y ∈ LinearMap.range Φ → χ' (x * y) = χ' x * χ' y := by
    intro x y hx hy
    rw [hrange] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨t, rfl⟩ := hz
      rw [hχ'mul_gen t x hx, hχ'red]
    | zero => rw [mul_zero, hχ'zero, mul_zero]
    | add y z hy hz ihy ihz =>
      have hy' : y ∈ LinearMap.range Φ := by rw [hrange]; exact hy
      have hz' : z ∈ LinearMap.range Φ := by rw [hrange]; exact hz
      rw [mul_add, hχ'add _ _ (hmulmem _ _ hx hy') (hmulmem _ _ hx hz'), ihy, ihz, hχ'add _ _ hy' hz', mul_add]
    | smul r y hy ihy =>
      have hy' : y ∈ LinearMap.range Φ := by rw [hrange]; exact hy
      rw [mul_smul_comm, hχ'smul _ _ (hmulmem _ _ hx hy'), ihy, hχ'smul _ _ hy', mul_left_comm]

  have hone : (1 : B) ∈ LinearMap.range Φ := by
    rw [← map_one red, hrange]; exact Submodule.subset_span (Set.mem_range_self _)
  have hχ'one : χ' 1 = 1 := by rw [← map_one red, hχ'red, map_one]

  let χ : ↥(Algebra.adjoin κ (Set.range red)) →ₐ[κ] κ :=
    { toFun := fun x => χ' (x : B)
      map_one' := by change χ' 1 = 1; exact hχ'one
      map_mul' := fun x y => by
        change χ' ((x : B) * (y : B)) = χ' (x : B) * χ' (y : B)
        exact hχ'mul _ _ (hmem.mp x.2) (hmem.mp y.2)
      map_zero' := by change χ' 0 = 0; exact hχ'zero
      map_add' := fun x y => by
        change χ' ((x : B) + (y : B)) = χ' (x : B) + χ' (y : B)
        exact hχ'add _ _ (hmem.mp x.2) (hmem.mp y.2)
      commutes' := fun r => by
        change χ' (algebraMap κ B r) = r
        rw [Algebra.algebraMap_eq_smul_one, hχ'smul _ _ hone, hχ'one, mul_one] }
  refine ⟨χ, fun t => ?_⟩
  change χ' (red t) = ρ t
  exact hχ'red t

end S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot
end P2MW
export P2MW.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot (solution)
