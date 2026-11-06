-- Prove2me | Definitions.Def_AdvMultiplayer_floorProg
-- name    : AdvMultiplayer_floorProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:18.792617+00:00
-- url     : https://prove2.me/theorems/90865b88-8a45-4f39-948a-c0a2f044d3f2
-- title:
--   Ticked real sums, floors and powers
-- statement:
--   The protocol is written as a program in the published real-RAM cost model: each read and each real operation or comparison costs one tick. This module adds the ticked sum and difference, repeated squaring, and the floor. The floor is not a primitive: it is computed by doubling and binary search with ticked comparisons, in a number of ticks proportional to the bit length bound of its argument.
--
--   **Formalization Note.** Section 8 counts exact arithmetic operations and does not list the floor; a unit-cost floor is a much stronger machine, so it is not assumed.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 8, p.48

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_rle
import Definitions.Def_LNTopology_Hermetization_rmul
import Definitions.Def_LNTopology_Hermetization_rdiv

open LNTopology.Hermetization

namespace AdvMultiplayer

/-- Ticked real sum. Gan, arXiv:2610.05688, Section 8 (exact arithmetic operations). -/
noncomputable def radd (x y : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure (x + y)

/-- Ticked real difference. Gan, arXiv:2610.05688, Section 8. -/
noncomputable def rsub (x y : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure (x - y)

/-- **The floor as a ticked search.** Gan, arXiv:2610.05688, Section 8, p.48 lists exact arithmetic
operations and does not list the floor among them, and a real RAM with unit-cost floor is much
stronger than one without. So a floor is not a free primitive: `floorProg fuel x` computes `⌊x⌋` by
doubling and then a binary search with ticked comparisons, in `O(fuel)` ticks.

**Formalization Note.** For `0 ≤ x < 2^fuel` the result is `⌊x⌋`; for `x < 0` it is `0`; for larger
`x` it is `2^fuel - 1`. Each call site passes a fuel exceeding the bit length of every value it can
receive on a valid input, and a domain check rejects the capped value where it matters. -/
noncomputable def floorProg (fuel : ℕ) (x : ℝ) : StateM ℕ ℕ := do
  let mut pw : ℝ := 1
  let mut pn : ℕ := 1
  for _ in List.range fuel do
    tick 1
    pw ← rmul pw 2
    pn := 2 * pn
  let mut acc : ℝ := 0
  let mut accN : ℕ := 0
  for _ in List.range fuel do
    tick 1
    pw ← rdiv pw 2
    pn := pn / 2
    let c ← radd acc pw
    let ok ← rle c x
    if ok then
      acc := c
      accN := accN + pn
  pure accN

/-- `x^n` by repeated squaring, for `n < 2^fuel` (Section 8, p.50). -/
noncomputable def powProg (fuel : ℕ) (x : ℝ) (n : ℕ) : StateM ℕ ℝ := do
  let mut res : ℝ := 1
  let mut base : ℝ := x
  for k in List.range fuel do
    tick 1
    if n.testBit k then
      res ← rmul res base
    base ← rmul base base
  pure res

end AdvMultiplayer


