-- Prove2me | Definitions.Def_TightClock_Supplement_ClockProg_settle
-- name    : TightClock_Supplement_ClockProg_settle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:03:08.732579+00:00
-- url     : https://prove2.me/theorems/e707a6b0-be65-4fa8-adb4-4614579f34a4
-- title:
--   Next visible action of a clock program
-- statement:
--   The **next visible action** of a clock program: perform internal steps until the program either returns a value or makes an offer. If the program never does either (it computes forever without offering), the result is "none".
--
--   **Formalization Note** Defined through the least number of internal steps after which the step is visible.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_ClockProg_step

set_option autoImplicit false

open Classical

namespace TightClock.Supplement

/-- The next visible step of a clock program: perform internal steps until the program either
returns (`done`) or makes an offer (`ask`). `none` if it runs forever without offers. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3,
p.13 (PDF 16).

**Formalization Note** `settle.stepN k x` is the result after at most `k` internal steps; the
least `k` at which the step is visible is taken. -/
noncomputable def ClockProg.settle {n : ℕ} {α : Type} (x : ClockProg n α) : Option (ProgStep n α) :=
  if h : ∃ k, ∀ y, settle.stepN k x ≠ .tau y then some (settle.stepN (Nat.find h) x) else none
where
  /-- At most `k` internal steps of `x`, stopping at the first visible step. -/
  stepN : ℕ → ClockProg n α → ProgStep n α
    | 0, x => .tau x
    | k + 1, x =>
      match x.step with
      | .tau y => stepN k y
      | s => s

end TightClock.Supplement


