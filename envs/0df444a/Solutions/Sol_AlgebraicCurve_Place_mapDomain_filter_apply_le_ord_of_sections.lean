-- Prove2me | solution 1 for AlgebraicCurve.Place.mapDomain_filter_apply_le_ord_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9b279e5e-a384-5921-820c-3600562b4b72

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections

set_option autoImplicit false

open AlgebraicCurve

namespace Ws49
namespace LscEngine
section GenericInduction
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {k E : Type*} [Field k] [Field E] [Algebra k E]
open Classical in

theorem penA_mapDomain_filter_apply (r : Place K F → Place k E)
    (S : Place K F → Prop) (D : Divisor K F) (v : Place k E) :
    Finsupp.mapDomain r (D.filter S) v = ∑ W ∈ D.support with (S W ∧ r W = v), D W := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finsupp.support_filter, Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [Finsupp.single_apply, Finsupp.filter_apply]
  by_cases hS : S W <;> by_cases hr : r W = v <;> simp [hS, hr]

open Classical in

theorem penA_lsc_sum_le_of_slots (𝒪 : ValuationSubring F) (ρ : 𝒪 →+* E)
    (hker : ∀ x : 𝒪, ρ x ≠ 0 → IsUnit x)
    (r : Place K F → Place k E) (S : Place K F → Prop) (v : Place k E)
    (hE : ∀ (f : F) (h : f ∈ 𝒪), (∀ W, S W → r W = v → 0 ≤ W.ord f) → 0 ≤ v.ord (ρ ⟨f, h⟩))
    (hP : ∀ Q, S Q → r Q = v → ∃ (s : F) (hs : s ∈ 𝒪),
      Q.ord s = 1 ∧ (∀ W, S W → r W = v → W ≠ Q → W.ord s = 0) ∧ v.ord (ρ ⟨s, hs⟩) = 1)
    (f : F) (h : f ∈ 𝒪) (hr : ρ ⟨f, h⟩ ≠ 0)
    (D : Divisor K F) (hD : ∀ W, D W = W.ord f)
    (hreg : ∀ W, S W → r W = v → 0 ≤ D W) :
    Finsupp.mapDomain r (D.filter S) v ≤ v.ord (ρ ⟨f, h⟩) := by
  suffices H : ∀ n : ℕ, ∀ (f : F) (h : f ∈ 𝒪), ρ ⟨f, h⟩ ≠ 0 →
      ∀ D : Divisor K F,
        (∀ W, S W → r W = v → D W = W.ord f) → (∀ W, S W → r W = v → 0 ≤ D W) →
        Finsupp.mapDomain r (D.filter S) v = n → (n : ℤ) ≤ v.ord (ρ ⟨f, h⟩) by
    have hnn : 0 ≤ Finsupp.mapDomain r (D.filter S) v := by
      rw [penA_mapDomain_filter_apply]
      exact Finset.sum_nonneg fun W hW =>
        hreg W (Finset.mem_filter.mp hW).2.1 (Finset.mem_filter.mp hW).2.2
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
    rw [hn]
    exact H n f h hr D (fun W _ _ => hD W) hreg hn
  intro n
  induction n with
  | zero =>
    intro f h _ D hD hreg _
    exact_mod_cast hE f h fun W hW hWv => (hD W hW hWv) ▸ hreg W hW hWv
  | succ n ih =>
    intro f h hr D hD hreg hn
    obtain ⟨Q, hQmem, hQpos⟩ : ∃ Q ∈ D.support.filter (fun W => S W ∧ r W = v), 0 < D Q := by
      by_contra hcon
      simp only [not_exists, not_and, not_lt] at hcon
      have hle : ∑ W ∈ D.support with (S W ∧ r W = v), D W ≤ 0 := Finset.sum_nonpos hcon
      rw [← penA_mapDomain_filter_apply, hn] at hle
      omega
    obtain ⟨-, hSQ, hrQ⟩ := Finset.mem_filter.mp hQmem
    obtain ⟨s, hs, hsQ, hsW, hsv⟩ := hP Q hSQ hrQ
    have hρs : ρ ⟨s, hs⟩ ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at hsv; exact zero_ne_one hsv
    obtain ⟨τ, hut⟩ := (hker ⟨s, hs⟩ hρs).exists_right_inv
    have hst : s * (τ : F) = 1 := congrArg Subtype.val hut
    have hs0 : s ≠ 0 := left_ne_zero_of_mul_eq_one hst
    have hτ0 : (τ : F) ≠ 0 := right_ne_zero_of_mul_eq_one hst
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hr (by rw [show (⟨(0 : F), h⟩ : 𝒪) = 0 from Subtype.ext rfl, map_zero])
    have hg : f * (τ : F) ∈ 𝒪 := mul_mem h τ.2
    have hρg : ρ ⟨f * τ, hg⟩ = ρ ⟨f, h⟩ * ρ τ := by rw [← map_mul]; rfl
    have hρτ : ρ ⟨s, hs⟩ * ρ τ = 1 := by rw [← map_mul, hut, map_one]
    have hρτ0 : ρ τ ≠ 0 := right_ne_zero_of_mul_eq_one hρτ
    have hordτ : v.ord (ρ τ) = -1 := by
      have h1 := v.ord_mul hρs hρτ0
      rw [hρτ, Place.ord_one, hsv] at h1
      omega
    have hρg0 : ρ ⟨f * τ, hg⟩ ≠ 0 := by rw [hρg]; exact mul_ne_zero hr hρτ0
    have hordg : v.ord (ρ ⟨f * τ, hg⟩) = v.ord (ρ ⟨f, h⟩) - 1 := by
      rw [hρg, v.ord_mul hr hρτ0, hordτ]; ring
    have hordτW : ∀ W : Place K F, W.ord (τ : F) = -W.ord s := by
      intro W
      have h1 := W.ord_mul hs0 hτ0
      rw [hst, Place.ord_one] at h1
      omega
    set D' : Divisor K F := D - Finsupp.single Q (1 : ℤ) with hD'def
    have hD' : ∀ W, S W → r W = v → D' W = W.ord (f * τ) := by
      intro W hW hWv
      rw [hD'def, Finsupp.sub_apply, W.ord_mul hf0 hτ0, hordτW W, ← hD W hW hWv, Finsupp.single_apply]
      by_cases hQW : Q = W
      · subst hQW; rw [if_pos rfl, hsQ]; omega
      · rw [if_neg hQW, hsW W hW hWv (Ne.symm hQW)]; simp
    have hreg' : ∀ W, S W → r W = v → 0 ≤ D' W := by
      intro W hW hWv
      rw [hD'def, Finsupp.sub_apply, Finsupp.single_apply]
      by_cases hQW : Q = W
      · subst hQW; simp; omega
      · rw [if_neg hQW]; simpa using hreg W hW hWv
    have hn' : Finsupp.mapDomain r (D'.filter S) v = n := by
      have h1 : Finsupp.mapDomain r
          ((Finsupp.single Q (1 : ℤ) : Divisor K F).filter S) v = 1 := by
        simp [Finsupp.filter_single_of_pos, hSQ, hrQ]
      rw [hD'def, Finsupp.filter_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, hn, h1]
      push_cast; ring
    have hih := ih (f * τ) hg hρg0 D' hD' hreg' hn'
    rw [hordg] at hih
    push_cast
    omega

end GenericInduction

end Ws49.LscEngine

open Classical in

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] {k E : Type*} [Field k] [Field E] [Algebra k E]
    (𝒪 : ValuationSubring F) (ρ : 𝒪 →+* E)
    (hker : ∀ x : 𝒪, ρ x ≠ 0 → IsUnit x)
    (r : Place K F → Place k E) (S : Place K F → Prop) (v : Place k E)
    (hE : ∀ (f : F) (h : f ∈ 𝒪), (∀ W, S W → r W = v → 0 ≤ W.ord f) → 0 ≤ v.ord (ρ ⟨f, h⟩))
    (hP : ∀ Q, S Q → r Q = v → ∃ (s : F) (hs : s ∈ 𝒪),
      Q.ord s = 1 ∧ (∀ W, S W → r W = v → W ≠ Q → W.ord s = 0) ∧ v.ord (ρ ⟨s, hs⟩) = 1)
    (f : F) (h : f ∈ 𝒪) (hr : ρ ⟨f, h⟩ ≠ 0)
    (D : Divisor K F) (hD : ∀ W, D W = W.ord f)
    (hreg : ∀ W, S W → r W = v → 0 ≤ D W) :
    Finsupp.mapDomain r (D.filter S) v ≤ v.ord (ρ ⟨f, h⟩) :=
  Ws49.LscEngine.penA_lsc_sum_le_of_slots 𝒪 ρ hker r S v hE hP f h hr D hD hreg

end S_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections
end P2MW
export P2MW.S_AlgebraicCurve_Place_mapDomain_filter_apply_le_ord_of_sections (solution)
