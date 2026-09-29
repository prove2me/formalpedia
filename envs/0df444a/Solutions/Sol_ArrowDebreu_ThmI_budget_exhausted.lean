-- Prove2me | solution 1 for ArrowDebreu.ThmI.budget_exhausted
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:06:00.541493+00:00
-- url     : https://prove2.me/submissions/e69cca04-6deb-49e4-8990-15d44856a70a

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI

theorem solution {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E)
    (hIIIb : AssumptionIIIb E) (hIIIc : AssumptionIIIc E)
    (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ)
    (h2 : Condition2 E p x y) :
    ∀ i, p ⬝ᵥ x i = income E p y i := by
  intro i
  obtain ⟨⟨hxX, hxb⟩, hmax⟩ := h2 i
  by_contra hne
  have hlt : p ⬝ᵥ x i < income E p y i := lt_of_le_of_ne hxb hne
  obtain ⟨x', hx'X, hux'⟩ := hIIIb i (x i) hxX
  set d : ℝ := income E p y i - p ⬝ᵥ x i with hd
  set a : ℝ := p ⬝ᵥ x' - p ⬝ᵥ x i with ha
  have hdpos : 0 < d := by rw [hd]; linarith
  set e : ℝ := |a| + 1 with he
  have hepos : 0 < e := by rw [he]; positivity
  set t : ℝ := min (1/2) (d / e) with ht
  have htpos : 0 < t := lt_min (by norm_num) (div_pos hdpos hepos)
  have htlt : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hta : t * a ≤ d := by
    calc t * a ≤ t * |a| := mul_le_mul_of_nonneg_left (le_abs_self a) htpos.le
      _ ≤ t * e := mul_le_mul_of_nonneg_left (by rw [he]; linarith) htpos.le
      _ ≤ (d / e) * e := mul_le_mul_of_nonneg_right (min_le_right _ _) hepos.le
      _ = d := div_mul_cancel₀ d hepos.ne'
  have hzX : t • x' + (1 - t) • x i ∈ E.X i :=
    (hII i).2.1 hx'X hxX htpos.le (by linarith) (by ring)
  have hzb : t • x' + (1 - t) • x i ∈ budgetSet E p y i := by
    refine ⟨hzX, ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [ha] at hta; rw [hd] at hta
    nlinarith
  have h1 := hmax _ hzb
  have h3 := hIIIc i x' hx'X (x i) hxX hux' t htpos htlt
  linarith
