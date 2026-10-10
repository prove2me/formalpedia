-- Prove2me | solution 1 for ActuarialValuation.quotaShareFiniteMenu_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:07:52.578215+00:00
-- url     : https://prove2.me/submissions/fc893cf1-ed7c-4b11-9a68-845b65081ce5

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Max
import Definitions.Def_actuarial_quotaShareCapitalObjective
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {A : Type*} [Fintype A] [Nonempty A] (r : A → ℝ)
    (q claim loading capital : ℝ) :
    ∃ a : A, ∀ b : A,
      quotaShareCapitalObjective q claim (r a) loading capital ≤
        quotaShareCapitalObjective q claim (r b) loading capital := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset A)
    (fun x => quotaShareCapitalObjective q claim (r x) loading capital)
    (Finset.univ_nonempty)
  refine ⟨a, ?_⟩
  intro b
  exact ha b (Finset.mem_univ b)
