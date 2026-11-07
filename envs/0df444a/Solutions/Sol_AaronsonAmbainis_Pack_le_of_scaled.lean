-- Prove2me | solution 1 for AaronsonAmbainis.Pack.le_of_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:33.485028+00:00
-- url     : https://prove2.me/submissions/eefb05b5-d98a-4f3c-958b-2ef1d62c48b5

import Definitions.Def_AaronsonAmbainis_Pack_Scaled
import Definitions.Def_AaronsonAmbainis_Pack_Packing

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
namespace AaronsonAmbainis.Pack
theorem _root_.solution (L C : ℝ) (d : ℕ)
    (key : ∀ M : ℕ, 0 < M → (M : ℝ) ^ 2 * L ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C) :
    L ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 := by
  by_contra hcon
  have hεpos : 0 < L - Real.pi ^ 2 * (d : ℝ) ^ 2 := by linarith [not_le.mp hcon]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  -- `C ≥ 0` is not assumed; `|C|` is used instead
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * (d : ℝ) ^ 2 * Real.pi + 4 * (d : ℝ) ^ 2 + |C| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 * Real.pi :=
      mul_nonneg (mul_nonneg (by norm_num) hd2) hpi.le
    have h2 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 := mul_nonneg (by norm_num) hd2
    linarith [abs_nonneg C]
  obtain ⟨M, hMgt⟩ := exists_nat_gt (K / (L - Real.pi ^ 2 * (d : ℝ) ^ 2))
  have hMr : (0 : ℝ) < (M : ℝ) := lt_of_le_of_lt (div_nonneg hK0 hεpos.le) hMgt
  have hMpos : 0 < M := Nat.cast_pos.mp hMr
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hMpos
  have h1 := key M hMpos
  -- `M² ε ≤ 4 d² π M + 4 d² + C`
  have h2 : (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)
      ≤ 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C := by
    have hexp : (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C
        = (M : ℝ) ^ 2 * (Real.pi ^ 2 * (d : ℝ) ^ 2)
          + (4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C) := by ring
    rw [hexp] at h1
    calc (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)
        = (M : ℝ) ^ 2 * L - (M : ℝ) ^ 2 * (Real.pi ^ 2 * (d : ℝ) ^ 2) := by ring
      _ ≤ 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C := by linarith
  -- `4 d² π M + 4 d² + C ≤ K M` because `M ≥ 1`
  have h3 : 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C ≤ K * (M : ℝ) := by
    have ha : 4 * (d : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (M : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg (by norm_num) hd2) hM1
    have hb : C ≤ |C| * (M : ℝ) :=
      (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hM1)
    have hc : K * (M : ℝ) = 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 * (M : ℝ)
        + |C| * (M : ℝ) := by rw [hK]; ring
    rw [hc]; linarith
  -- divide by `M`
  have h4 : (M : ℝ) * ((M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)) ≤ (M : ℝ) * K := by
    calc (M : ℝ) * ((M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2))
        = (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) := by ring
      _ ≤ K * (M : ℝ) := h2.trans h3
      _ = (M : ℝ) * K := mul_comm _ _
  have h5 : (M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) ≤ K := le_of_mul_le_mul_left h4 hMr
  have h6 : K < (M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) := (div_lt_iff₀ hεpos).mp hMgt
  exact absurd h5 (not_le.mpr h6)
end AaronsonAmbainis.Pack
