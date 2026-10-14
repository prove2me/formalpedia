-- Prove2me | solution 1 for Apery.inner_bound_cap
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T21:17:52.345052+00:00
-- url     : https://prove2.me/submissions/5da33f2a-e117-4f7a-93fe-8c362dfb228f

/-
# The inner-range determinant bound with capped weights (source `Apery/Arith/InnerWeights.lean`)

For $p = 2m+1$, dimensions $L$ with $\sum_c L_c = 37n$ and the zero-class condition
$\mathrm{tmin} \le 2L_0 + (b_0 - 4)/2$, the determinant $\Delta n$ satisfies
$v_p^G(\Delta n) \ge 2\sum_s \mathrm{wcap}(s)$ with the capped weights
$\mathrm{wcap}(a,i) = \min(2i + (b_a-4)/2, \mathrm{tmin})$ on the zero class.
The file ports `Apery/Arith/InnerWeights.lean` (`tmin_le`, `winner_ACI`, `wcap_ACI`, the capped
framework `inner_bound_cap`), importing the proved platform theorems `Apery.class_frame` and
`Apery.classCount_eq`. Faithful port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit
import Theorems.Thm_Apery_class_frame
import Theorems.Thm_Apery_classCount_eq

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Finset Polynomial

namespace Apery

variable {m : ℕ}

lemma tmin_le (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) {c : Fin (m + 1)} (hc : c ≠ 0) :
    tmin hm L b ≤ topw L b c :=
  Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)

/-- The abstract class inequality. -/
theorem winner_ACI (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (hP : ∀ a c : Fin (m + 1), a ≠ 0 → c ≠ 0 → topw L b a - 1 ≤ topw L b c)
    (hZ : ∀ a : Fin (m + 1), a ≠ 0 → topw L b a - 1 ≤ 2 * L 0 + (b 0 - 4) / 2)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (a : Fin (m + 1)) :
    winner hm L b s + winner hm L b t + 4 ≤
      b a + (if a = 0 then 2 else 1) * ((nu L s a : ℚ) + nu L t a) := by
  -- basic facts
  have F1 : ∀ u : Σ a : Fin (m + 1), Fin (L a), u.1 ≠ 0 →
      winner hm L b u ≤ topw L b u.1 - 1 := by
    intro u hu
    unfold winner topw; rw [if_neg hu]
    have : (u.2 : ℚ) ≤ L u.1 - 1 := by
      have := u.2.isLt; have : (u.2 : ℕ) + 1 ≤ L u.1 := this
      have : ((u.2 : ℕ) : ℚ) + 1 ≤ L u.1 := by exact_mod_cast this
      linarith
    linarith
  have F3 : ∀ u : Σ a : Fin (m + 1), Fin (L a), ∀ c : Fin (m + 1), c ≠ 0 →
      winner hm L b u ≤ topw L b c := by
    intro u c hc
    by_cases hu : u.1 = 0
    · unfold winner; rw [if_pos hu]
      exact (min_le_right _ _).trans (tmin_le hm L b hc)
    · linarith [F1 u hu, hP u.1 c hu hc]
  have Fz : ∀ u : Σ a : Fin (m + 1), Fin (L a),
      winner hm L b u ≤ (if u.1 = 0 then 2 * (u.2 : ℚ) else 2 * (L 0 : ℚ)) + (b 0 - 4) / 2 := by
    intro u
    by_cases hu : u.1 = 0
    · unfold winner; rw [if_pos hu, if_pos hu]; exact min_le_left _ _
    · rw [if_neg hu]; linarith [F1 u hu, hZ u.1 hu]
  unfold nu
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, show (((0 : Fin (m + 1)) : ℕ)) = 0 from rfl]
    have h1 := Fz s; have h2 := Fz t
    by_cases hs : s.1 = 0 <;> by_cases ht : t.1 = 0
    · rw [if_pos hs.symm, if_pos ht.symm]; rw [if_pos hs] at h1; rw [if_pos ht] at h2; linarith
    · rw [if_pos hs.symm, if_neg (Ne.symm ht)]; rw [if_pos hs] at h1; rw [if_neg ht] at h2
      linarith
    · rw [if_neg (Ne.symm hs), if_pos ht.symm]; rw [if_neg hs] at h1; rw [if_pos ht] at h2
      linarith
    · rw [if_neg (Ne.symm hs), if_neg (Ne.symm ht)]; rw [if_neg hs] at h1; rw [if_neg ht] at h2
      linarith
  · rw [if_neg ha, one_mul]
    have htop : b a - 4 = 2 * (topw L b a - L a) := by unfold topw; ring
    by_cases hs : a = s.1 <;> by_cases ht : a = t.1
    · rw [if_pos hs, if_pos ht]
      have e1 : winner hm L b s = (s.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner; rw [if_neg (hs ▸ ha)]; simp only [hs]
      have e2 : winner hm L b t = (t.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner; rw [if_neg (ht ▸ ha)]; simp only [ht]
      rw [e1, e2]; linarith
    · rw [if_pos hs, if_neg ht]
      have e1 : winner hm L b s = (s.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner; rw [if_neg (hs ▸ ha)]; simp only [hs]
      have := F3 t a ha
      rw [e1]; unfold topw at this; linarith
    · rw [if_neg hs, if_pos ht]
      have e2 : winner hm L b t = (t.2 : ℚ) + (b a - 4) / 2 := by
        unfold winner; rw [if_neg (ht ▸ ha)]; simp only [ht]
      have := F3 s a ha
      rw [e2]; unfold topw at this; linarith
    · rw [if_neg hs, if_neg ht]
      have h1 := F3 s a ha; have h2 := F3 t a ha
      unfold topw at h1 h2; linarith

/-- **Inner-range determinant bound** for an allocation satisfying (P) and (Z). -/
theorem inner_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hP : ∀ a c : Fin (m + 1), a ≠ 0 → c ≠ 0 →
      topw L (Bse p (40 * n) (3 * n)) a - 1 ≤ topw L (Bse p (40 * n) (3 * n)) c)
    (hZ : ∀ a : Fin (m + 1), a ≠ 0 → topw L (Bse p (40 * n) (3 * n)) a - 1 ≤
      2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, winner hm1 L (Bse p (40 * n) (3 * n)) s) := by
  refine class_frame hp5 hm n L hL _ hsep hK hdeg fun s t c => ?_
  rw [classCount_eq hm]
  exact winner_ACI hm1 L _ hP hZ s t (ccls hm c)

/-! ### Capped weights: validity needs only the zero-class condition -/

theorem wcap_ACI (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (hZ : tmin hm L b ≤ 2 * L 0 + (b 0 - 4) / 2)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (a : Fin (m + 1)) :
    wcap hm L b s + wcap hm L b t + 4 ≤
      b a + (if a = 0 then 2 else 1) * ((nu L s a : ℚ) + nu L t a) := by
  have F3 : ∀ u : Σ a : Fin (m + 1), Fin (L a), ∀ c : Fin (m + 1), c ≠ 0 →
      wcap hm L b u ≤ topw L b c := fun u c hc =>
    (min_le_right _ _).trans (tmin_le hm L b hc)
  have Fraw : ∀ u : Σ a : Fin (m + 1), Fin (L a), wcap hm L b u ≤ wraw L b u :=
    fun u => min_le_left _ _
  have Fz : ∀ u : Σ a : Fin (m + 1), Fin (L a),
      wcap hm L b u ≤ (if u.1 = 0 then 2 * (u.2 : ℚ) else 2 * (L 0 : ℚ)) + (b 0 - 4) / 2 := by
    intro u
    by_cases hu : u.1 = 0
    · rw [if_pos hu]; have := Fraw u; unfold wraw at this; rw [if_pos hu] at this; exact this
    · rw [if_neg hu]; exact (min_le_right _ _).trans hZ
  unfold nu
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, show (((0 : Fin (m + 1)) : ℕ)) = 0 from rfl]
    have h1 := Fz s; have h2 := Fz t
    by_cases hs : s.1 = 0 <;> by_cases ht : t.1 = 0
    · rw [if_pos hs.symm, if_pos ht.symm]; rw [if_pos hs] at h1; rw [if_pos ht] at h2; linarith
    · rw [if_pos hs.symm, if_neg (Ne.symm ht)]; rw [if_pos hs] at h1; rw [if_neg ht] at h2
      linarith
    · rw [if_neg (Ne.symm hs), if_pos ht.symm]; rw [if_neg hs] at h1; rw [if_pos ht] at h2
      linarith
    · rw [if_neg (Ne.symm hs), if_neg (Ne.symm ht)]; rw [if_neg hs] at h1; rw [if_neg ht] at h2
      linarith
  · rw [if_neg ha, one_mul]
    have hraw : ∀ u : Σ a : Fin (m + 1), Fin (L a), a = u.1 →
        wcap hm L b u ≤ (u.2 : ℚ) + (b a - 4) / 2 := by
      intro u hu
      have := Fraw u
      unfold wraw at this; rw [if_neg (hu ▸ ha)] at this; simpa only [hu] using this
    by_cases hs : a = s.1 <;> by_cases ht : a = t.1
    · rw [if_pos hs, if_pos ht]
      have := hraw s hs; have := hraw t ht; linarith
    · rw [if_pos hs, if_neg ht]
      have := hraw s hs; have h2 := F3 t a ha
      unfold topw at h2; linarith
    · rw [if_neg hs, if_pos ht]
      have := hraw t ht; have h2 := F3 s a ha
      unfold topw at h2; linarith
    · rw [if_neg hs, if_neg ht]
      have h1 := F3 s a ha; have h2 := F3 t a ha
      unfold topw at h1 h2; linarith

/-- **Inner-range determinant bound** with capped weights; only the zero-class condition. -/
theorem inner_bound_cap_aux {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hZ : tmin hm1 L (Bse p (40 * n) (3 * n)) ≤
      2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, wcap hm1 L (Bse p (40 * n) (3 * n)) s) := by
  refine class_frame hp5 hm n L hL _ hsep hK hdeg fun s t c => ?_
  rw [classCount_eq hm]
  exact wcap_ACI hm1 L _ hZ s t (ccls hm c)
end Apery

end Port0

open Finset Polynomial in
theorem solution {p : ℕ} [Fact p.Prime] {m : ℕ} (hp5 : 5 ≤ p) (hm : 2 * m + 1 = p) (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (hsep : Apery.Sep p (Apery.PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hZ : Apery.tmin hm1 L (Apery.Bse p (40 * n) (3 * n)) ≤
      2 * L 0 + (Apery.Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    Apery.GV p (Apery.Δ n) (2 * ∑ s, Apery.wcap hm1 L (Apery.Bse p (40 * n) (3 * n)) s) :=
  Apery.inner_bound_cap_aux hp5 hm hm1 n L hL hsep hK hdeg hZ
