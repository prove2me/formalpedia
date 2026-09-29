-- Prove2me | Definitions.Def_OnlinePrimalDual_Framework_alg1X
-- name    : OnlinePrimalDual_Framework_alg1X
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:33:12.805486+00:00
-- url     : https://prove2.me/theorems/c7902f4f-0a33-4a77-9339-f807e89968d7
-- title:
--   Algorithm 1's (the basic discrete algorithm) final primal value
-- statement:
--   Algorithm 1's own update rule (p. 118, step (1a)), applied once per inner-loop iteration to
--   every `i ∈ S(j)` while processing constraint `j`, is `x_i ← x_i(1 + 1/c_i) + 1/(|S(j)|·c_i)`,
--   using *that round's own* `|S(j)|`, not a fixed bound. Since the order in which rounds touch a
--   given `i` changes the compounded value, `alg1X inst ord t i` takes an explicit arrival order
--   `ord : List J` on the constraints and replays, for each round `j` (restricted to `ord`, in
--   order, filtered to `i ∈ S(j)`), that round's own affine update `t_j` times in a row, starting
--   from `x_i = 0`. This is the algorithm's own recurrence exactly, with no round-uniform
--   substitution.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 118, Algorithm 1, step (1a)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- The final value Algorithm 1 (the basic discrete algorithm, p. 118, PDF p. 29) assigns to
primal variable `xᵢ`. Algorithm 1's own update rule (p. 118, step (1a)) is
`xᵢ ← xᵢ(1 + 1/cᵢ) + 1/(|S(j)|cᵢ)`, applied once per inner-loop iteration to every `i ∈ S(j)`
while constraint `j` is being processed — using *that round's own* `|S(j)| = (inst.S j).card`,
not a fixed bound. Since which rounds touch `i`, and in what order, matters (the multiplicative
`(1+1/cᵢ)` factor compounds differently depending on interleaving), the true final value needs an
explicit arrival order on the constraints; `ord : List J` is that order (the sequence in which
the online algorithm sees constraints `j`, one entry per element of `J`). For a fixed `i`, we walk
`ord` restricted to the rounds `j` with `i ∈ S j`, in order, and for each such round apply the
round's own affine update `t j` times in a row (all `t j` increments of round `j` share the same
`|S(j)|`, since `S(j)` does not change mid-round), starting from `x = 0`. This is Algorithm 1's
own recurrence, exactly, with no substitution. -/
noncomputable def alg1X {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (inst : CoveringInstance I J) (ord : List J) (t : J → ℕ) (i : I) : ℝ :=
  (ord.filter (fun j => i ∈ inst.S j)).foldl
    (fun x j => (fun y => y * (1 + 1 / inst.c i) + 1 / ((inst.S j).card * inst.c i))^[t j] x) 0

end OnlinePrimalDual.Framework


