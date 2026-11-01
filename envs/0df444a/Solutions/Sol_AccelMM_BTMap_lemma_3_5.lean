-- Prove2me | solution 1 for AccelMM.BTMap.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:31:15.781502+00:00
-- url     : https://prove2.me/submissions/578c5ff4-c53a-45dd-ac26-81d590086730

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model
import Theorems.Thm_AccelMM_BTMap_lemma_3_3

open AccelMM.BTMap in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ) (hω : 0 ≤ ω)
    (x y : E n) (hx : x ∈ box ω) (hy : y ∈ box ω) :
    rhoSurr α β d x y - rho α β d x ≥
      -((1 / 2 * Real.exp (2 * ω) * degM d) / 2) * ‖x - y‖ ^ 2 := by
  have h := AccelMM.BTMap.lemma_3_3 d ω hω x y hx hy
  have e : rhoSurr α β d x y - rho α β d x = surr d x y - loglik d x := by
    unfold rhoSurr rho; ring
  rw [e]; exact h
