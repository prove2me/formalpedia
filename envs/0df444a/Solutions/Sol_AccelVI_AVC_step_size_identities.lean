-- Prove2me | solution 1 for AccelVI.AVC.step_size_identities
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:09:25.961773+00:00
-- url     : https://prove2.me/submissions/6b5e34cf-1bd2-4ad4-aad7-1e397a9e434f

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

set_option autoImplicit false
open AccelVI.AVC

theorem solution (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    1 + 1 / kappa lam - 2 * alphaAVC lam = 0 ∧
    (1 - alphaAVC lam) * (1 + gammaAVC lam) = alphaAVC lam * lam * (1 + gammaAVC lam) ∧
    alphaAVC lam * lam * (1 + gammaAVC lam) = 1 - Real.sqrt (1 / kappa lam) ∧
    alphaAVC lam * gammaAVC lam * lam = (1 - alphaAVC lam) * gammaAVC lam ∧
    (1 - alphaAVC lam) * gammaAVC lam = alphaAVC lam - Real.sqrt (1 / kappa lam) ∧
    alphaAVC lam - Real.sqrt (1 / kappa lam) = 1 / 2 * (1 - Real.sqrt (1 / kappa lam)) ^ 2 := by
  have hp : 0 < 1 + lam := by linarith
  have hm : 0 < 1 - lam := by linarith
  have hκ : 1 / kappa lam = (1 - lam) / (1 + lam) := by
    unfold kappa; field_simp
  rw [hκ]
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt ((1 - lam) / (1 + lam)) := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hq2 : q ^ 2 = (1 - lam) / (1 + lam) := by
    rw [hq]; exact Real.sq_sqrt (div_nonneg hm.le hp.le)
  have hs : Real.sqrt (1 - lam ^ 2) = q * (1 + lam) := by
    have : (q * (1 + lam)) ^ 2 = 1 - lam ^ 2 := by
      rw [mul_pow, hq2]; field_simp; ring
    rw [← this, Real.sqrt_sq (mul_nonneg hq0 hp.le)]
  have hγ : gammaAVC lam = (1 - q * (1 + lam)) / lam := by
    unfold gammaAVC; rw [hs]
  have hα : alphaAVC lam = 1 / (1 + lam) := rfl
  rw [hγ, hα]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp <;> ring
  · field_simp <;> ring
  · field_simp <;> ring
  · field_simp <;> ring
  · field_simp <;> ring
  · field_simp
    have hq2' : (1 + lam) * q ^ 2 = 1 - lam := by rw [hq2]; field_simp
    linear_combination (-1 : ℝ) * hq2'
