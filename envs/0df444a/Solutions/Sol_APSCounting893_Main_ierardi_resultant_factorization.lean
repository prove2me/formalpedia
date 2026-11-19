-- Prove2me | solution 1 for APSCounting893.Main.ierardi_resultant_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:34:01.969931+00:00
-- url     : https://prove2.me/submissions/05569d2b-2a99-47a2-b54d-5e6e6e5b5e95

import Theorems.Thm_APSCounting893_Main_epsilon_limit_set_finite
import Theorems.Thm_APSCounting893_Main_epsilon_resultant_product
import Definitions.Def_APSCounting893_Main_Resultant
set_option autoImplicit false
open APSCounting893.Main
theorem solution (F : ReducedMap) (D : LineData F) (lambda : Affine ℂ (F.n + 1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    ∃ S : Finset (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient),
      (S : Set _) = epsilonLimitSet F D.c D.alpha degrees ∧
      ∃ (mu : (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) → ℕ)
        (representatives : (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) →
          (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient)),
        (∀ z ∈ S, 0 < mu z ∧ ∃ a : PuiseuxAmbient, a ≠ 0 ∧ representatives z = a • z) ∧
        trailingEpsilonResultant (resultantFor F D.c D.alpha lambda degrees) =
          ∏ z ∈ S, HAtPoint F lambda (representatives z) ^ mu z := by
  classical
  let hf := epsilon_limit_set_finite F D.c D.alpha degrees hdegrees
  let S := hf.toFinset
  have hS : (S : Set _) = epsilonLimitSet F D.c D.alpha degrees := hf.coe_toFinset
  exact ⟨S,hS,epsilon_resultant_product F D lambda hsep degrees hdegrees S hS⟩
