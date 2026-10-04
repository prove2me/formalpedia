-- Prove2me | solution 1 for AssumptionsOfPhysics.theoretical_iInter_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:27:17.772678+00:00
-- url     : https://prove2.me/submissions/9f77dc49-3b35-4786-a940-9d1199ef91e8

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) (f : ℕ → Set Ω)
    (hf : ∀ n, f n ∈ D.theoretical) : (⋂ n, f n) ∈ D.theoretical := by
  have h : (⋂ n, f n) = (⋃ n, (f n)ᶜ)ᶜ := by
    rw [Set.compl_iUnion]; simp only [compl_compl]
  rw [h]
  exact NegFinConjCountDisj.compl
    (NegFinConjCountDisj.iUnion _ (fun n => NegFinConjCountDisj.compl (hf n)))
