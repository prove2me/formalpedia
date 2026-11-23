-- Prove2me | solution 1 for AdditiveConvexity.sensitivity_preserved
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:36:41.457857+00:00
-- url     : https://prove2.me/submissions/abe22396-32f6-44e2-bda7-7c4fea197484

import Mathlib
import Definitions.Def_AdditiveConvexity_chainDomain
import Definitions.Def_AdditiveConvexity_IncreasingInCoord
import Definitions.Def_AdditiveConvexity_SlopeLEInCoord
import Definitions.Def_AdditiveConvexity_transformSet

set_option autoImplicit false

open AdditiveConvexity

namespace AdditiveConvexity.SensProof

def localSerialSet (I : Set ℝ) {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {z | z ∈ chainDomain I n ∧ (∀ i : Fin (n + 1), k < i.val → z i = x i) ∧
    ∀ i : Fin (n + 1), i.val ≤ k → x i ≤ z i}

noncomputable def runMin {n : ℕ} (δ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i)).inf'
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩⟩ δ

theorem runMin_le {n : ℕ} (δ : Fin (n + 1) → ℝ) {i j : Fin (n + 1)} (h : j ≤ i) :
    runMin δ i ≤ δ j :=
  Finset.inf'_le δ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩ :
    j ∈ Finset.univ.filter (fun j' : Fin (n + 1) => j' ≤ i))

theorem runMin_exists {n : ℕ} (δ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ∃ j, j ≤ i ∧ runMin δ i = δ j := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf'
    (⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩⟩ :
      (Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i)).Nonempty) δ
  exact ⟨j, (Finset.mem_filter.mp hj).2, he⟩

theorem runMin_anti {n : ℕ} (δ : Fin (n + 1) → ℝ) {i i' : Fin (n + 1)} (h : i ≤ i') :
    runMin δ i' ≤ runMin δ i :=
  Finset.le_inf' _ _ (fun j hj => runMin_le δ (le_trans (Finset.mem_filter.mp hj).2 h))

theorem runMin_nonneg {n : ℕ} (δ : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h : ∀ j, j ≤ i → 0 ≤ δ j) : 0 ≤ runMin δ i :=
  Finset.le_inf' _ _ (fun j hj => h j (Finset.mem_filter.mp hj).2)

theorem runMin_zero {n : ℕ} (δ : Fin (n + 1) → ℝ) : runMin δ 0 = δ 0 :=
  le_antisymm (runMin_le δ le_rfl) (Finset.le_inf' _ _ (fun j hj => by
    have : j = 0 := le_antisymm (Finset.mem_filter.mp hj).2 (Fin.zero_le _)
    rw [this]))

theorem improve {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ}
    {f : (Fin (n + 1) → ℝ) → ℝ}
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ chainDomain I n) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ localSerialSet I k x) : ∃ z' ∈ transformSet I k x, f z' ≤ f z := by
  obtain ⟨⟨hz0, hzm⟩, hztail, hzge⟩ := hz
  obtain ⟨hx0, hxm⟩ := hx
  let δ : Fin (n + 1) → ℝ := fun i => z i - x i
  let z' : Fin (n + 1) → ℝ := fun i => if i.val ≤ k then x i + runMin δ i else x i
  have hz'le : ∀ i, z' i ≤ z i := by
    intro i
    by_cases hi : i.val ≤ k
    · have := runMin_le δ (le_refl i)
      simp only [z', if_pos hi]
      simp only [δ] at this
      linarith
    · simp only [z', if_neg hi]
      rw [hztail i (by omega)]
  have hz'0 : z' 0 = z 0 := by
    simp only [z', Fin.val_zero, Nat.zero_le, if_true, runMin_zero, δ]
    ring
  have hz'mono : Monotone z' := by
    intro i i' hii'
    have hii'v : i.val ≤ i'.val := hii'
    by_cases hi' : i'.val ≤ k
    · have hi : i.val ≤ k := le_trans hii'v hi'
      simp only [z', if_pos hi, if_pos hi']
      obtain ⟨j, hj, he⟩ := runMin_exists δ i'
      rw [he]
      by_cases hji : j ≤ i
      · have h1 := runMin_le δ hji
        have h2 := hxm hii'
        linarith
      · push Not at hji
        have h1 := runMin_le δ (le_refl i)
        have h2 := hzm hji.le
        have h3 := hxm hj
        simp only [δ] at h1 ⊢
        linarith
    · by_cases hi : i.val ≤ k
      · simp only [z', if_pos hi, if_neg hi']
        have h1 := runMin_le δ (le_refl i)
        have h2 := hzm hii'
        have h3 := hztail i' (by omega)
        simp only [δ] at h1
        linarith
      · simp only [z', if_neg hi, if_neg hi']
        exact hxm hii'
  let w : ℕ → Fin (n + 1) → ℝ := fun r i => if i.val < r then z' i else z i
  have hw_mem : ∀ r, 1 ≤ r → w r ∈ chainDomain I n := by
    intro r hr
    refine ⟨?_, ?_⟩
    · have : (w r) 0 = z' 0 := by
        simp only [w]
        rw [if_pos (by simp only [Fin.val_zero]; omega)]
      rw [this, hz'0]
      exact hz0
    · intro i i' hii'
      have hii'v : i.val ≤ i'.val := hii'
      simp only [w]
      by_cases hi : i.val < r <;> by_cases hi' : i'.val < r
      · rw [if_pos hi, if_pos hi']; exact hz'mono hii'
      · rw [if_pos hi, if_neg hi']; exact (hz'le i).trans (hzm hii')
      · omega
      · rw [if_neg hi, if_neg hi']; exact hzm hii'
  have hw_step : ∀ r, 1 ≤ r → (hrk : r ≤ k) → f (w (r + 1)) ≤ f (w r) := by
    intro r hr hrk
    have hrn : r < n + 1 := by omega
    apply hmono ⟨r, hrn⟩ (show 1 ≤ r by omega) (show r ≤ k by omega) (w (r + 1))
      (hw_mem _ (by omega)) (w r) (hw_mem r hr)
    · intro i hi
      have hiv : i.val ≠ r := fun h => hi (Fin.ext h)
      simp only [w]
      by_cases h1 : i.val < r
      · rw [if_pos (by omega), if_pos h1]
      · rw [if_neg (by omega), if_neg h1]
    · simp only [w]
      rw [if_pos (show (⟨r, hrn⟩ : Fin (n + 1)).val < r + 1 from Nat.lt_succ_self r),
        if_neg (show ¬ (⟨r, hrn⟩ : Fin (n + 1)).val < r from lt_irrefl r)]
      exact hz'le _
  have hw1 : w 1 = z := by
    funext i
    simp only [w]
    by_cases h : i.val < 1
    · rw [if_pos h]
      have : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [this, hz'0]
    · rw [if_neg h]
  have hwk : w (k + 1) = z' := by
    funext i
    simp only [w]
    by_cases h : i.val < k + 1
    · rw [if_pos h]
    · rw [if_neg h]
      simp only [z', if_neg (show ¬ i.val ≤ k by omega)]
      exact hztail i (by omega)
  have hiter : ∀ s, s ≤ k → f (w (k + 1)) ≤ f (w (k + 1 - s)) := by
    intro s
    induction s with
    | zero => intro _; exact le_rfl
    | succ s ih =>
      intro hs
      have h1 := ih (by omega)
      rw [show k + 1 - s = k - s + 1 by omega] at h1
      have h2 := hw_step (k - s) (by omega) (by omega)
      rw [show k + 1 - (s + 1) = k - s by omega]
      exact h1.trans h2
  have hfin := hiter k le_rfl
  rw [show k + 1 - k = 1 by omega, hw1, hwk] at hfin
  refine ⟨z', ⟨⟨by rw [hz'0]; exact hz0, hz'mono⟩, ?_, ?_, ?_⟩, hfin⟩
  · intro i hi
    simp only [z', if_neg (show ¬ i.val ≤ k by omega)]
  · intro i hi
    simp only [z', if_pos hi]
    have := runMin_nonneg δ i (fun j hj => by
      have hjv : j.val ≤ i.val := hj
      have := hzge j (by omega)
      simp only [δ]
      linarith)
    linarith
  · intro i j hij hj
    have hijv : i.val ≤ j.val := hij
    simp only [z', if_pos hj, if_pos (le_trans hijv hj)]
    have := runMin_anti δ hij
    linarith

theorem isLeast_serial {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ}
    {f : (Fin (n + 1) → ℝ) → ℝ}
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ chainDomain I n) (v : ℝ) :
    IsLeast (f '' transformSet I k x) v ↔ IsLeast (f '' localSerialSet I k x) v := by
  have hsub : transformSet I k x ⊆ localSerialSet I k x := by
    rintro z ⟨hzc, htail, hnn, -⟩
    exact ⟨hzc, htail, fun i hi => by linarith [hnn i hi]⟩
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hlb⟩
    refine ⟨⟨z, hsub hz, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hle⟩ := improve hk1 hkn hmono hx y hy
    exact (hlb ⟨y', hy', rfl⟩).trans hle
  · rintro ⟨⟨z, hz, rfl⟩, hlb⟩
    obtain ⟨z', hz', hle⟩ := improve hk1 hkn hmono hx z hz
    have : f z ≤ f z' := hlb ⟨z', hsub hz', rfl⟩
    refine ⟨⟨z', hz', le_antisymm hle this⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hlb ⟨y, hsub hy, rfl⟩

end AdditiveConvexity.SensProof

open AdditiveConvexity.SensProof in
theorem solution {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {I : Set ℝ}
    (hI : Convex ℝ I) {f g : (Fin (n + 1) → ℝ) → ℝ}
    (hmono : ∀ m : Fin (n + 1), 1 ≤ m.val → m.val ≤ k → IncreasingInCoord (chainDomain I n) f m)
    (hg : ∀ x ∈ chainDomain I n, IsLeast (f '' transformSet I k x) (g x))
    (m : Fin (n + 1)) (hm : 1 ≤ m.val) (a : ℝ)
    (hf : SlopeLEInCoord (chainDomain I n) f m a) :
    SlopeLEInCoord (chainDomain I n) g m a := by
  intro x hx x' hx' hoff hle
  obtain ⟨⟨z, hz, hfz⟩, -⟩ := hg x hx
  obtain ⟨⟨hz0, hzm⟩, hztail, hznn, hzdec⟩ := hz
  obtain ⟨hx0, hxm⟩ := hx
  obtain ⟨hx'0, hx'm⟩ := hx'
  have hm0 : (0 : Fin (n + 1)) ≠ m := by
    intro h; rw [← h] at hm; simp at hm
  by_cases hmk : m.val ≤ k
  · have hfx : f x ≤ f x' := hmono m hm hmk x ⟨hx0, hxm⟩ x' ⟨hx'0, hx'm⟩ hoff hle
    have hfx' : f x' - f x ≤ a * (x' m - x m) := hf x ⟨hx0, hxm⟩ x' ⟨hx'0, hx'm⟩ hoff hle
    have haprod : 0 ≤ a * (x' m - x m) := by linarith
    let z' : Fin (n + 1) → ℝ := Function.update z m (max (z m) (x' m))
    have hz'_chain : z' ∈ chainDomain I n := by
      refine ⟨by simp [z', hm0, hz0], ?_⟩
      intro i j hij
      by_cases hi : i = m <;> by_cases hj : j = m
      · subst hi; rw [hj]
      · subst hi
        simp only [z', Function.update_self, Function.update_of_ne hj]
        apply max_le (hzm hij)
        have h1 : x' i ≤ x' j := hx'm hij
        rw [← hoff j hj] at h1
        by_cases hjk : j.val ≤ k
        · linarith [hznn j hjk]
        · rw [hztail j (by omega)]; exact h1
      · subst hj
        simp only [z', Function.update_of_ne hi, Function.update_self]
        exact (hzm hij).trans (le_max_left _ _)
      · simp only [z', Function.update_of_ne hi, Function.update_of_ne hj]
        exact hzm hij
    have hz'_ser : z' ∈ localSerialSet I k x' := by
      refine ⟨hz'_chain, ?_, ?_⟩
      · intro i hik
        have him : i ≠ m := by intro h; subst h; omega
        simp only [z', Function.update_of_ne him, hztail i hik, hoff i him]
      · intro i hik
        by_cases him : i = m
        · subst him; simp [z']
        · simp only [z', Function.update_of_ne him, ← hoff i him]
          linarith [hznn i hik]
    have hg' := ((isLeast_serial hk1 hkn hmono ⟨hx'0, hx'm⟩ (g x')).mp (hg x' ⟨hx'0, hx'm⟩)).2
      ⟨z', hz'_ser, rfl⟩
    by_cases hzx' : x' m ≤ z m
    · have hz'eq : z' = z := by
        funext i
        by_cases hi : i = m
        · subst hi; simp [z', max_eq_left hzx']
        · simp [z', hi]
      rw [hz'eq, hfz] at hg'
      linarith
    · push Not at hzx'
      have hxm_le : x m ≤ z m := by linarith [hznn m hmk]
      have ha0 : 0 ≤ a := by
        by_contra ha0
        push Not at ha0
        have : a * (x' m - x m) < 0 := mul_neg_of_neg_of_pos ha0 (by linarith)
        linarith
      have hslope := hf z ⟨hz0, hzm⟩ z' hz'_chain
        (fun i hi => by simp [z', hi])
        (by simp [z'])
      have hz'm : z' m = x' m := by simp [z', max_eq_right hzx'.le]
      rw [hz'm] at hslope
      have : a * (x' m - z m) ≤ a * (x' m - x m) := by nlinarith
      linarith
  · have hzm_eq : z m = x m := hztail m (by omega)
    let z' : Fin (n + 1) → ℝ := Function.update z m (x' m)
    have hz'_chain : z' ∈ chainDomain I n := by
      refine ⟨by simp [z', hm0, hz0], ?_⟩
      intro i j hij
      by_cases hi : i = m <;> by_cases hj : j = m
      · subst hi; rw [hj]
      · subst hi
        have hjk : k < j.val := by have : i.val ≤ j.val := hij; omega
        simp only [z', Function.update_self, Function.update_of_ne hj, hztail j hjk, hoff j hj]
        exact hx'm hij
      · subst hj
        simp only [z', Function.update_of_ne hi, Function.update_self]
        exact (hzm hij).trans (by rw [hzm_eq]; exact hle)
      · simp only [z', Function.update_of_ne hi, Function.update_of_ne hj]
        exact hzm hij
    have hz'_tr : z' ∈ transformSet I k x' := by
      refine ⟨hz'_chain, ?_, ?_, ?_⟩
      · intro i hik
        by_cases him : i = m
        · subst him; simp [z']
        · simp [z', him, hztail i hik, hoff i him]
      · intro i hik
        have him : i ≠ m := by intro h; subst h; omega
        simp only [z', Function.update_of_ne him, ← hoff i him]
        exact hznn i hik
      · intro i j hij hjk
        have hjv : i.val ≤ j.val := hij
        have him : i ≠ m := by intro h; subst h; omega
        have hjm : j ≠ m := by intro h; subst h; omega
        simp only [z', Function.update_of_ne him, Function.update_of_ne hjm,
          ← hoff i him, ← hoff j hjm]
        exact hzdec i j hij hjk
    have hg' := (hg x' ⟨hx'0, hx'm⟩).2 ⟨z', hz'_tr, rfl⟩
    have hslope := hf z ⟨hz0, hzm⟩ z' hz'_chain
      (fun i hi => by simp [z', hi])
      (by simp [z', hzm_eq, hle])
    simp only [z', Function.update_self, hzm_eq] at hslope
    linarith
