-- Prove2me | solution 1 for AlgMechDesign.Additive.exists_agent_many_tasks
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:03:36.995746+00:00
-- url     : https://prove2.me/submissions/91b2f7ae-4cf3-4faa-8683-7c7eec30c178

import Definitions.Def_AlgMechDesign_Additive_Model
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false
open AlgMechDesign.Additive

theorem solution {n k : ℕ} [NeZero n] (hk : n ^ 2 ≤ k) (x : Fin k → Fin n) :
    ∃ i : Fin n, n ≤ (taskSet x i).card := by
  obtain ⟨i, hi, hcard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := x) (s := Finset.univ) (t := Finset.univ) (n := n)
    (by simp) Finset.univ_nonempty (by simpa [pow_two] using hk)
  exact ⟨i, hcard⟩
