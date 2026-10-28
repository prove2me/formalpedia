-- Prove2me | solution 1 for AntitoneOn.of_hasDerivAt_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T16:29:44.122702+00:00
-- url     : https://prove2.me/submissions/acca5ebc-53b9-4f84-98fd-8dc1b7ea6148

import Mathlib

-- carved verbatim out of submission 108d25ac-4cbb-466b-9bd4-122188ee844b, lines 94-104

section
open Set

theorem solution {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, g x ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

end
