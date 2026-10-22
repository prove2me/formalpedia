-- Prove2me | solution 1 for AssortSearch.SearchQC.D_K_pos_increasing
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:54:59.558669+00:00
-- url     : https://prove2.me/submissions/0e1ed578-afa1-49cc-abc0-fe0863fbb7c1

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_ProofTerms
set_option autoImplicit false
open AssortSearch.SearchQC

lemma as_g_pos (y : ℝ) (hy : 0 < y) : 0 < (y - 2) * Real.exp y + y + 2 := by
  have hmono : StrictMonoOn (fun y : ℝ => (y - 2) * Real.exp y + y + 2) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · apply Continuous.continuousOn
      fun_prop
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := ht
      have h1 : HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2)
          ((1 * Real.exp t + (t - 2) * Real.exp t) + 1) t :=
        ((((hasDerivAt_id t).sub_const 2).mul (Real.hasDerivAt_exp t)).add (hasDerivAt_id t)).add_const 2
      rw [h1.deriv]
      have h2 : -t + 1 < Real.exp (-t) := Real.add_one_lt_exp (by linarith)
      rw [Real.exp_neg] at h2
      have h3 := Real.exp_pos t
      have h4 : (1 - t) * Real.exp t < 1 := by
        have := mul_lt_mul_of_pos_right h2 h3
        rw [inv_mul_cancel₀ h3.ne'] at this
        linarith
      nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) hy
  simpa using this

theorem solution (lam VS : ℝ) (hlam : 0 < lam) (hVS : 0 < VS) :
    (∀ x ∈ Set.Ici (0 : ℝ), 0 < Dfn lam VS x ∧ 0 < Kfn lam VS x) ∧
      StrictMonoOn (Dfn lam VS) (Set.Ici 0) ∧
      StrictMonoOn (Kfn lam VS) (Set.Ici 0) ∧
      StrictMonoOn (fun x => Kfn lam VS x / Dfn lam VS x) (Set.Ici 0) := by
  have hKpos : ∀ x : ℝ, 0 ≤ x → 0 < Kfn lam VS x := by
    intro x hx
    unfold Kfn
    have : 0 < lam * (x + VS) := by positivity
    have := Real.add_one_lt_exp (show lam * (x + VS) ≠ 0 from this.ne')
    linarith
  have hDpos : ∀ x : ℝ, 0 ≤ x → 0 < Dfn lam VS x := by
    intro x hx
    unfold Dfn
    have h0 : 0 < lam * (x + VS) := by positivity
    have := Real.add_one_lt_exp (show lam * (x + VS) ≠ 0 from h0.ne')
    have h1 : 0 ≤ lam * x / VS * (x + VS) := by positivity
    nlinarith
  refine ⟨fun x hx => ⟨hDpos x hx, hKpos x hx⟩, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := ha
    unfold Dfn
    have h1 : Real.exp (lam * (a + VS)) < Real.exp (lam * (b + VS)) :=
      Real.exp_lt_exp.2 (by nlinarith)
    have h2 : lam * a / VS * (a + VS) ≤ lam * b / VS * (b + VS) := by
      have hb0 : 0 ≤ b := ha0.trans hab.le
      apply mul_le_mul _ (by linarith) (by linarith) (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab.le hlam.le) hVS.le
    linarith
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := ha
    unfold Kfn
    have hy : 0 < lam * (b - a) := mul_pos hlam (by linarith)
    have h1 : lam * (b - a) + 1 < Real.exp (lam * (b - a)) := Real.add_one_lt_exp hy.ne'
    have h2 : 1 < Real.exp (lam * (a + VS)) := Real.one_lt_exp_iff.2 (by positivity)
    have e : Real.exp (lam * (b + VS)) = Real.exp (lam * (a + VS)) * Real.exp (lam * (b - a)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    nlinarith [mul_pos (sub_pos.2 h2) (sub_pos.2 h1), Real.exp_pos (lam * (a + VS))]
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · apply ContinuousOn.div
      · unfold Kfn; apply Continuous.continuousOn; fun_prop
      · unfold Dfn; apply Continuous.continuousOn; fun_prop
      · intro x hx; exact (hDpos x hx).ne'
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := hx
      have hl : HasDerivAt (fun x : ℝ => lam * (x + VS)) lam x := by
        simpa using ((hasDerivAt_id x).add_const VS).const_mul lam
      have hE := hl.exp
      have hK : HasDerivAt (Kfn lam VS) (Real.exp (lam * (x + VS)) * lam - lam) x := by
        have := (hE.sub_const 1).sub hl
        exact this
      have hD : HasDerivAt (Dfn lam VS)
          (Real.exp (lam * (x + VS)) * lam + (lam / VS * (x + VS) + lam * x / VS)) x := by
        have h1 : HasDerivAt (fun x : ℝ => lam * x / VS) (lam / VS) x := by
          simpa using (((hasDerivAt_id x).const_mul lam).div_const VS)
        have h2 := h1.mul ((hasDerivAt_id x).add_const VS)
        have := (hE.sub_const 1).add h2
        have h3 : HasDerivAt (Dfn lam VS)
            (Real.exp (lam * (x + VS)) * lam + (lam / VS * (id x + VS) + lam * x / VS * 1)) x := this
        exact h3.congr_deriv (by simp)
      have hq : HasDerivAt (fun x => Kfn lam VS x / Dfn lam VS x) _ x := hK.div hD (hDpos x hx0.le).ne'
      rw [hq.deriv]
      have hnum : (Real.exp (lam * (x + VS)) * lam - lam) * Dfn lam VS x - Kfn lam VS x *
          (Real.exp (lam * (x + VS)) * lam + (lam / VS * (x + VS) + lam * x / VS))
          = lam / VS * (VS + x) * ((lam * (x + VS) - 2) * Real.exp (lam * (x + VS)) + lam * (x + VS) + 2) := by
        unfold Dfn Kfn
        field_simp
        ring
      rw [hnum]
      have hg := as_g_pos (lam * (x + VS)) (by positivity)
      have hDx := hDpos x hx0.le
      positivity
