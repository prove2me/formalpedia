-- Prove2me | solution 1 for Aggmetrics.skew_invariant_iff_factors_through_recall_specificity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:52:46.18412+00:00
-- url     : https://prove2.me/submissions/4ea7a451-d8c7-4c8e-884f-7fd758609b09

import Mathlib
import Definitions.Def_Aggmetrics_Basic

set_option autoImplicit true
open Finset
open Aggmetrics
namespace Aggmetrics
theorem _root_.solution
    (M : ℝ → ℝ → ℝ → ℝ → ℝ) :
    (∀ tp fp fn tn : ℝ, 0 < tp + fn → 0 < fp + tn →
      ∀ lam mu : ℝ, 0 < lam → 0 < mu →
        M (lam * tp) (mu * fp) (lam * fn) (mu * tn) = M tp fp fn tn)
    ↔
    (∃ g : ℝ → ℝ → ℝ, ∀ tp fp fn tn : ℝ, 0 < tp + fn → 0 < fp + tn →
      M tp fp fn tn = g (tp / (tp + fn)) (tn / (fp + tn))) := by
  constructor
  · intro hskew
    refine ⟨fun r s => M r (1 - s) (1 - r) s, ?_⟩
    intro tp fp fn tn htpfn hfptn
    have hlam : (0:ℝ) < 1 / (tp + fn) := by positivity
    have hmu : (0:ℝ) < 1 / (fp + tn) := by positivity
    have h := hskew tp fp fn tn htpfn hfptn (1 / (tp + fn)) (1 / (fp + tn)) hlam hmu
    have e1 : 1 / (tp + fn) * tp = tp / (tp + fn) := by ring
    have e2 : 1 / (tp + fn) * fn = 1 - tp / (tp + fn) := by
      field_simp [htpfn.ne']; ring
    have e3 : 1 / (fp + tn) * fp = 1 - tn / (fp + tn) := by
      field_simp [hfptn.ne']; ring
    have e4 : 1 / (fp + tn) * tn = tn / (fp + tn) := by ring
    rw [e1, e2, e3, e4] at h
    exact h.symm
  · rintro ⟨g, hg⟩ tp fp fn tn htpfn hfptn lam mu hlam hmu
    have htpfn' : 0 < lam * tp + lam * fn := by nlinarith [mul_pos hlam htpfn]
    have hfptn' : 0 < mu * fp + mu * tn := by nlinarith [mul_pos hmu hfptn]
    rw [hg (lam*tp) (mu*fp) (lam*fn) (mu*tn) htpfn' hfptn', hg tp fp fn tn htpfn hfptn]
    have hr : (lam * tp) / (lam * tp + lam * fn) = tp / (tp + fn) := by
      rw [show lam*tp+lam*fn = lam*(tp+fn) from by ring, mul_div_mul_left _ _ hlam.ne']
    have hs : (mu * tn) / (mu * fp + mu * tn) = tn / (fp + tn) := by
      rw [show mu*fp+mu*tn = mu*(fp+tn) from by ring, mul_div_mul_left _ _ hmu.ne']
    rw [hr, hs]
end Aggmetrics
