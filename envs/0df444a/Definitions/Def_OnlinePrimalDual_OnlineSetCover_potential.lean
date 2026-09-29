-- Prove2me | Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential
-- name    : OnlinePrimalDual_OnlineSetCover_potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:39:27.16843+00:00
-- url     : https://prove2.me/theorems/85a9cf96-d10e-4a04-81e0-79989fd013de
-- title:
--   The algorithm's potential function Φ
-- statement:
--   `Φ = ∑_{e∉C̄} n^{2we} + n·exp((1/2α)∑_s(cs·χC(s) − 3ws·cs·log n))`, where `n = |E|` is the
--   number of elements, `χC` is `C`'s characteristic function, and `α` is the current guess of
--   `c(COPT)`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 136-137, PDF p. 47-48

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy

namespace OnlinePrimalDual.OnlineSetCover

open Classical in
/-- The potential function driving the deterministic online algorithm (p. 136-137, PDF p. 47-48):
`Φ = ∑_{e∉C̄} n^{2we} + n·exp((1/2α)∑_s(cs·χC(s) − 3ws·cs·log n))`, where `n = |X|` is the (known
in advance, per `SetCoverInstance`'s docstring) number of elements, `χC` is `C`'s characteristic
function, and `α` is the current guess of `c(COPT)`. Both the sum over uncovered elements and the
inner sum over sets are literal transcriptions of the displayed formula; `n` is cast from
`Fintype.card E` rather than taken as a free parameter, matching the book's use of the same
symbol `n` for both "number of elements" and the potential's base/exponent. -/
noncomputable def potential {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (C : Finset T) (α : ℝ) : ℝ :=
  let n : ℝ := (Fintype.card E : ℝ)
  (∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), n ^ (2 * elementWeight inst w e)) +
    n * Real.exp ((1 / (2 * α)) *
      ∑ t : T, (inst.c t * (if t ∈ C then (1 : ℝ) else 0) - 3 * w t * inst.c t * Real.log n))

end OnlinePrimalDual.OnlineSetCover


