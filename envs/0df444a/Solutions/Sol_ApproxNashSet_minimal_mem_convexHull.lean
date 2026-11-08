-- Prove2me | solution 1 for ApproxNashSet.minimal_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:31:44.742526+00:00
-- url     : https://prove2.me/submissions/9292ce7f-610c-465e-b3d5-60fdadf39517

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

open ApproxNashSet in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (i : ι)
    (S : Set (Obj n i)) :
    MinSet (convexHull ℝ S + {d : Obj n i | 0 ≤ d}) ⊆ convexHull ℝ S := by
  rintro y ⟨hy, hmin⟩
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_add.mp hy
  have hcP : c ∈ convexHull ℝ S + {d : Obj n i | 0 ≤ d} :=
    Set.mem_add.mpr ⟨c, hc, 0, (by show (0 : Obj n i) ≤ 0; exact le_refl _), add_zero c⟩
  have hle : c ≤ c + d := le_add_of_nonneg_right hd
  rw [← hmin c hcP hle]
  exact hc
