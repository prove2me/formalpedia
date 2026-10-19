-- Prove2me | solution 1 for AssortSearch.SearchQC.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:59:04.57499+00:00
-- url     : https://prove2.me/submissions/d0f608b4-bc5d-4884-ae01-fc94953a84f6

import Mathlib

set_option autoImplicit false

theorem solution (lam x VS : ℝ) (hlam : 0 < lam) (hW : 0 < x + VS) :
    2 - 2 * Real.exp (-(lam * (x + VS))) - lam * (x + VS) * Real.exp (-(lam * (x + VS)))
      - lam * (x + VS) < 0 := by
  have hw : 0 < lam * (x + VS) := mul_pos hlam hW
  generalize lam * (x + VS) = w at hw ⊢
  -- h(w) = w - 2 + (2+w) e^{-w}... we show 2 - 2e^{-w} - w e^{-w} - w < 0 via -h strictly anti
  set f : ℝ → ℝ := fun t => 2 - 2 * Real.exp (-t) - t * Real.exp (-t) - t with hf
  have hd : ∀ t : ℝ, HasDerivAt f (-(1 - (1 + t) * Real.exp (-t))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      have := (hasDerivAt_neg t).exp
      convert this using 1
      ring
    have h2 := ((((hasDerivAt_const t (2:ℝ)).sub (h1.const_mul 2)).sub
      ((hasDerivAt_id t).mul h1)).sub (hasDerivAt_id t))
    refine h2.congr_deriv ?_
    simp only [id]
    ring
  have hanti : StrictAntiOn f (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt) |>.continuousOn
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : 0 < t := ht
      rw [(hd t).deriv]
      have : 1 + t < Real.exp t := by
        have := Real.add_one_lt_exp (ne_of_gt ht')
        linarith
      have h3 : (1 + t) * Real.exp (-t) < 1 := by
        rw [Real.exp_neg]
        have := Real.exp_pos t
        rw [mul_inv_lt_iff₀ this]; linarith
      linarith
  have h0 : f 0 = 0 := by simp [hf]
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hw.le) hw
  rw [h0] at this
  exact this
