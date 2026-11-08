-- Prove2me | solution 1 for ApproxNashSet.remark_4_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:42:50.377926+00:00
-- url     : https://prove2.me/submissions/da261014-723e-485c-b266-2da19650f335

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

open ApproxNashSet in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (X : Set (Joint n)) (V G : Set (Joint n)) (hX : X = convexHull ℝ V) (hVG : V ⊆ G)
    (i : ι) (x : Joint n) (hx : x ∈ X) :
    minus n i x ∈ convexHull ℝ (minus n i '' G) := by
  have hlin : IsLinearMap ℝ (minus n i) :=
    ⟨fun a b => rfl, fun c a => rfl⟩
  have h1 : minus n i x ∈ minus n i '' convexHull ℝ V := ⟨x, hX ▸ hx, rfl⟩
  rw [hlin.image_convexHull] at h1
  exact convexHull_mono (Set.image_mono hVG) h1
