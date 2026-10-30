-- Prove2me | solution 1 for AssortOpt.HMF.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:19:55.81991+00:00
-- url     : https://prove2.me/submissions/8a53dd60-3c70-48d7-a225-cb4d64297ace

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

open AssortOpt.HMF

namespace HMFCore

variable {n : ℕ}

lemma take_succ_eq (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    ℓ.take (k + 1) = ℓ.take k ++ [ℓ[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

lemma mem_prefixes {D : ListDist n} {ρ : List (Fin n)} :
    ρ ∈ prefixes D ↔ ρ ≠ [] ∧ ∃ ℓ ∈ D.supp, ρ <+: ℓ := by
  unfold prefixes
  simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
  tauto

lemma prefixes_filter_eq (D : ListDist n) (ℓ : List (Fin n)) (hℓ : ℓ ∈ D.supp) :
    (prefixes D).filter (fun ρ => ρ <+: ℓ) =
      (Finset.range ℓ.length).image (fun k => ℓ.take (k + 1)) := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, mem_prefixes]
  constructor
  · rintro ⟨⟨hne, -⟩, hpre⟩
    have hlen : ρ.length ≤ ℓ.length := hpre.length_le
    have hpos : 0 < ρ.length := List.length_pos_iff.mpr hne
    refine ⟨ρ.length - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hpos]
    exact (List.prefix_iff_eq_take.mp hpre).symm
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨?_, ℓ, hℓ, List.take_prefix _ _⟩, List.take_prefix _ _⟩
    rw [take_succ_eq ℓ k hk]
    simp
    intro h; subst h; simp at hk

/-- Exchange of the sum over realizable prefixes with the sum over lists and positions. -/
lemma prefix_exchange (D : ListDist n) (G : List (Fin n) → ℝ) :
    ∑ ρ ∈ prefixes D, prefProb D ρ * G ρ =
      ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k ∈ Finset.range ℓ.length, G (ℓ.take (k + 1)) := by
  classical
  unfold prefProb
  have h1 : ∀ ρ, (∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ) * G ρ =
      ∑ ℓ ∈ D.supp, if ρ <+: ℓ then D.p ℓ * G ρ else 0 := by
    intro ρ
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ _
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [← Finset.sum_filter, ← Finset.mul_sum, prefixes_filter_eq D ℓ hℓ]
  congr 1
  rw [Finset.sum_image]
  intro a ha b hb hab
  have := congrArg List.length hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp [List.length_take] at this
  omega

/-- The stopping indicator at position `i` of `ℓ` (0 if out of range). -/
noncomputable def sv (φ : Policy n) (ℓ : List (Fin n)) (i : ℕ) : ℝ :=
  (ℓ[i]?.map (fun a => ind (φ a (ℓ.take i).toFinset))).getD 0

lemma sv_eq (φ : Policy n) (ℓ : List (Fin n)) (i : ℕ) (hi : i < ℓ.length) :
    sv φ ℓ i = ind (φ ℓ[i] (ℓ.take i).toFinset) := by
  unfold sv
  rw [List.getElem?_eq_getElem hi]
  rfl

lemma endPrice_take (r : Fin n → ℝ) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    endPrice r (ℓ.take (k + 1)) = r ℓ[k] := by
  unfold endPrice
  rw [take_succ_eq ℓ k hk, List.getLast?_concat]
  rfl

lemma getLast?_take (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    (ℓ.take (k + 1)).getLast? = some ℓ[k] := by
  rw [take_succ_eq ℓ k hk, List.getLast?_concat]

lemma dropLast_take (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    (ℓ.take (k + 1)).dropLast = ℓ.take k := by
  rw [take_succ_eq ℓ k hk, List.dropLast_concat]

lemma stopInd_take (φ : Policy n) (ℓ : List (Fin n)) (k : ℕ) (hk : k < ℓ.length) :
    stopInd φ (ℓ.take (k + 1)) = sv φ ℓ k * ∏ i ∈ Finset.range k, (1 - sv φ ℓ i) := by
  unfold stopInd
  rw [getLast?_take ℓ k hk]
  simp only
  rw [dropLast_take ℓ k hk, sv_eq φ ℓ k hk]
  congr 1
  have hlen : (ℓ.take k).length = k := by simp [List.length_take]; omega
  have e1 : ∀ k' : Fin (ℓ.take k).length,
      (1 - ind (φ ((ℓ.take k).get k') ((ℓ.take (k + 1)).take k').toFinset)) =
        (fun i => 1 - sv φ ℓ i) k'.1 := by
    intro k'
    have hk' : k'.1 < k := by have := k'.2; omega
    simp only
    rw [sv_eq φ ℓ k' (by omega), List.take_take, min_eq_left (by omega)]
    simp [List.getElem_take]
  rw [Finset.prod_congr rfl (fun k' _ => e1 k'), Finset.prod_range (fun i => 1 - sv φ ℓ i), hlen]

end HMFCore

namespace HMFCore

variable {n : ℕ}

lemma toFinset_take_mono (ℓ : List (Fin n)) {i j : ℕ} (hij : i ≤ j) :
    (ℓ.take i).toFinset ⊆ (ℓ.take j).toFinset := by
  intro a ha
  rw [List.mem_toFinset] at ha ⊢
  exact (List.take_prefix_take_left hij).subset ha

lemma insert_take (ℓ : List (Fin n)) (i : ℕ) (hi : i < ℓ.length) :
    insert ℓ[i] (ℓ.take i).toFinset = (ℓ.take (i + 1)).toFinset := by
  rw [take_succ_eq ℓ i hi, List.toFinset_append]
  ext a
  simp [or_comm]

lemma revPolicy_eq_lists (D : ListDist n) (r : Fin n → ℝ) (φ : Policy n) :
    revPolicy D r φ = ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k : Fin ℓ.length,
      r ℓ[k.1] * (sv φ ℓ k * ∏ i ∈ Finset.range k, (1 - sv φ ℓ i)) := by
  unfold revPolicy
  have h1 : ∀ ρ ∈ prefixes D, endPrice r ρ * prefProb D ρ * stopInd φ ρ =
      prefProb D ρ * (endPrice r ρ * stopInd φ ρ) := fun ρ _ => by ring
  rw [Finset.sum_congr rfl h1, prefix_exchange]
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  rw [Finset.sum_range (fun k => endPrice r (ℓ.take (k + 1)) * stopInd φ (ℓ.take (k + 1)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [endPrice_take r ℓ k k.2, stopInd_take φ ℓ k k.2]

end HMFCore


open AssortOpt.HMF HMFCore

namespace HMFProp3Aux

variable {n : ℕ}

lemma ind_le (a b : Bool) (h : a ≤ b) : ind a ≤ ind b := by
  cases a <;> cases b <;> simp_all [ind] <;> exact absurd h (by decide)

lemma bool_policy_rev (D : ListDist n) (r : Fin n → ℝ) (f : Finset (Fin n) → ℝ)
    (hf : IsIncreasingSetFn f) (hb : ∀ S, f S = 0 ∨ f S = 1) (h0 : f ∅ = 0) :
    revPolicy D r (fun j H => decide (f (insert j H) = 1)) = revSetFn D r f := by
  rw [revPolicy_eq_lists]
  unfold revSetFn
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [List.get_eq_getElem]
  congr 1
  set φ : Policy n := fun j H => decide (f (insert j H) = 1) with hφ
  have hsv : ∀ i (hi : i < ℓ.length), sv φ ℓ i =
      if f (ℓ.take (i + 1)).toFinset = 1 then 1 else 0 := by
    intro i hi
    rw [sv_eq φ ℓ i hi, hφ]
    have := insert_take ℓ i hi
    simp only [ind, this]
    by_cases h : f (ℓ.take (i + 1)).toFinset = 1 <;> simp [h]
  have hmono : ∀ i j, i ≤ j → f (ℓ.take i).toFinset ≤ f (ℓ.take j).toFinset :=
    fun i j hij => hf.1 (toFinset_take_mono ℓ hij)
  have hle1 : ∀ S, f S ≤ 1 := fun S => (hf.2 S).2
  rw [hsv k k.2]
  rcases hb (ℓ.take k).toFinset with hk0 | hk1
  · -- all earlier stopping indicators vanish
    have hprod : ∏ i ∈ Finset.range k, (1 - sv φ ℓ i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hsv i (by have := k.2; omega)]
      have : f (ℓ.take (i + 1)).toFinset ≤ 0 := hk0 ▸ hmono (i + 1) k (by omega)
      rw [if_neg (by linarith)]
      ring
    rw [hprod, hk0]
    rcases hb (ℓ.take (k + 1)).toFinset with h | h <;> simp [h]
  · -- k ≥ 1 and the factor at k - 1 vanishes
    have hkpos : 0 < k.1 := by
      rcases Nat.eq_zero_or_pos k.1 with h | h
      · exfalso
        rw [h, List.take_zero, List.toFinset_nil, h0] at hk1
        norm_num at hk1
      · exact h
    have hprod : ∏ i ∈ Finset.range k, (1 - sv φ ℓ i) = 0 := by
      apply Finset.prod_eq_zero (i := k.1 - 1) (Finset.mem_range.mpr (by omega))
      rw [hsv (k.1 - 1) (by have := k.2; omega), Nat.sub_add_cancel hkpos, if_pos hk1]
      ring
    have hk1' : f (ℓ.take (k + 1)).toFinset = 1 :=
      le_antisymm (hle1 _) (hk1 ▸ hmono k (k + 1) (by omega))
    rw [hprod, hk1, hk1']
    simp

/-- the constant-1 set function has zero revenue -/
lemma revSetFn_const (D : ListDist n) (r : Fin n → ℝ) (c : ℝ) :
    revSetFn D r (fun _ => c) = 0 := by
  unfold revSetFn
  simp

lemma revPolicy_false (D : ListDist n) (r : Fin n → ℝ) :
    revPolicy D r (fun _ _ => false) = 0 := by
  unfold revPolicy
  apply Finset.sum_eq_zero
  intro ρ _
  unfold stopInd
  cases ρ.getLast? <;> simp [ind]


open MeasureTheory

noncomputable def thr (v θ : ℝ) : ℝ := (Set.Iic v).indicator (1 : ℝ → ℝ) θ

lemma thr_integral (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    ∫ θ, thr v θ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = v := by
  unfold thr
  rw [integral_indicator_one measurableSet_Iic]
  rw [Measure.real, Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic v ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 v := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨b, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a, le_trans b h1⟩
  rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  ring

lemma thr_integrable (v : ℝ) :
    Integrable (thr v) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  unfold thr
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic

lemma revSetFn_integral (D : ListDist n) (r : Fin n → ℝ) (g : Finset (Fin n) → ℝ)
    (hg : ∀ S, g S ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun θ => revSetFn D r (fun S => thr (g S) θ))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    ∫ θ, revSetFn D r (fun S => thr (g S) θ) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      revSetFn D r g := by
  unfold revSetFn
  have hint : ∀ ℓ ∈ D.supp, Integrable (fun θ => D.p ℓ * ∑ k : Fin ℓ.length,
      r (ℓ.get k) * (thr (g (ℓ.take (k + 1)).toFinset) θ - thr (g (ℓ.take k).toFinset) θ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro ℓ _
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ (fun k _ => ?_)
    exact ((thr_integrable _).sub (thr_integrable _)).const_mul _
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [integral_const_mul]
  congr 1
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin ℓ.length)), Integrable (fun θ => r (ℓ.get k) *
      (thr (g (ℓ.take (k + 1)).toFinset) θ - thr (g (ℓ.take k).toFinset) θ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k _
    exact Integrable.const_mul (Integrable.sub (thr_integrable _) (thr_integrable _)) _
  rw [integral_finsetSum _ hk]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, integral_sub (thr_integrable _) (thr_integrable _),
    thr_integral _ (hg _).1 (hg _).2, thr_integral _ (hg _).1 (hg _).2]

lemma bool_opt (D : ListDist n) (r : Fin n → ℝ) :
    ∃ f : Finset (Fin n) → ℝ, IsIncreasingSetFn f ∧ (∀ S, f S = 0 ∨ f S = 1) ∧
      ∀ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g → revSetFn D r g ≤ revSetFn D r f := by
  classical
  let B : Finset (Finset (Fin n) → Bool) := Finset.univ.filter (fun b => Monotone b)
  have hBne : B.Nonempty := ⟨fun _ => false, by simp [B, monotone_const]⟩
  obtain ⟨b, hbB, hbmax⟩ := Finset.exists_max_image B
    (fun b => revSetFn D r (fun S => ind (b S))) hBne
  have hbmono : Monotone b := (Finset.mem_filter.mp hbB).2
  refine ⟨fun S => ind (b S), ⟨fun S S' h => ind_le _ _ (hbmono h), fun S => ?_⟩, fun S => ?_, ?_⟩
  · by_cases h : b S <;> simp [ind, h]
  · by_cases h : b S <;> simp [ind, h]
  · intro g hg
    obtain ⟨hint, heq⟩ := revSetFn_integral D r g hg.2
    rw [← heq]
    have hbound : ∀ θ, revSetFn D r (fun S => thr (g S) θ) ≤
        revSetFn D r (fun S => ind (b S)) := by
      intro θ
      let c : Finset (Fin n) → Bool := fun S => decide (θ ≤ g S)
      have hc : Monotone c := by
        intro S S' h
        simp only [c]
        by_cases h1 : θ ≤ g S
        · have : θ ≤ g S' := le_trans h1 (hg.1 h)
          simp [this]
        · simp [h1]
      have hcB : c ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have e : (fun S => thr (g S) θ) = (fun S => ind (c S)) := by
        funext S
        simp only [thr, Set.indicator_apply, Set.mem_Iic, ind, c, Pi.one_apply]
        by_cases h1 : θ ≤ g S <;> simp [h1]
      rw [e]
      exact hbmax c hcB
    calc ∫ θ, revSetFn D r (fun S => thr (g S) θ) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        ≤ ∫ θ, revSetFn D r (fun S => ind (b S)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
          integral_mono hint (integrable_const _) hbound
      _ = revSetFn D r (fun S => ind (b S)) := by
          rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
            Set.univ_inter, Real.volume_Ioc]
          simp

end HMFProp3Aux

open HMFProp3Aux in
theorem solution {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    (∃ f : Finset (Fin n) → ℝ, IsIncreasingSetFn f ∧ (∀ S, f S = 0 ∨ f S = 1) ∧
      ∀ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g → revSetFn D r g ≤ revSetFn D r f) ∧
    (∀ f : Finset (Fin n) → ℝ, IsIncreasingSetFn f → (∀ S, f S = 0 ∨ f S = 1) → f ∅ = 0 →
      IsMonotonePolicy (fun j H => decide (f (insert j H) = 1)) ∧
      revPolicy D r (fun j H => decide (f (insert j H) = 1)) = revSetFn D r f) ∧
    (∀ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g →
      ∃ φ : Policy n, IsMonotonePolicy φ ∧ revSetFn D r g ≤ revPolicy D r φ) := by
  have c2 : ∀ f : Finset (Fin n) → ℝ, IsIncreasingSetFn f → (∀ S, f S = 0 ∨ f S = 1) →
      f ∅ = 0 →
      IsMonotonePolicy (fun j H => decide (f (insert j H) = 1)) ∧
      revPolicy D r (fun j H => decide (f (insert j H) = 1)) = revSetFn D r f := by
    intro f hf hb h0
    refine ⟨?_, bool_policy_rev D r f hf hb h0⟩
    intro j H H' _ hHH'
    by_cases h1 : f (insert j H) = 1
    · have : f (insert j H') = 1 :=
        le_antisymm (hf.2 _).2 (h1 ▸ hf.1 (Finset.insert_subset_insert j hHH'))
      simp [h1, this]
    · simp [h1]
  refine ⟨bool_opt D r, c2, ?_⟩
  intro g hg
  obtain ⟨f, hf, hb, hopt⟩ := bool_opt D r
  rcases hb ∅ with h0 | h1
  · exact ⟨_, (c2 f hf hb h0).1, by rw [(c2 f hf hb h0).2]; exact hopt g hg⟩
  · have hconst : f = fun _ => 1 := by
      funext S
      exact le_antisymm (hf.2 S).2 (h1 ▸ hf.1 (Finset.empty_subset S))
    refine ⟨fun _ _ => false, fun _ _ _ _ _ => le_refl _, ?_⟩
    rw [revPolicy_false]
    have := hopt g hg
    rw [hconst, revSetFn_const] at this
    exact this
