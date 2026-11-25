-- Prove2me | solution 1 for Arxiv2610_39302.renderings_change_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:48:14.154118+00:00
-- url     : https://prove2.me/submissions/b77a5927-e18b-436e-a8ca-c9eb699bbf21

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

open Arxiv2610_39302 in
theorem solution {Z X : Type*} [Fintype Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal)
    (hObj : IsJEPAObjective p ℓ Om) (g : Z → X) (hg : Function.Injective g) :
    Function.Bijective
      (fun (f : Set.range g → Fin k → ℝ) (z : Z) => f ⟨g z, Set.mem_range_self z⟩) ∧
    ∀ f : X → Fin k → ℝ, modalityLoss p π ℓ Om g f = worldLoss p π ℓ Om (fun z => f (g z)) := by
  refine ⟨⟨fun f1 f2 h => ?_, fun h => ?_⟩, fun f => rfl⟩
  · funext ⟨x, z, hz⟩
    subst hz
    exact congrFun h z
  · classical
    refine ⟨fun x => h (Classical.choose x.2), ?_⟩
    funext z
    have hc := Classical.choose_spec (Set.mem_range_self (f := g) z)
    simp only
    rw [hg hc]
