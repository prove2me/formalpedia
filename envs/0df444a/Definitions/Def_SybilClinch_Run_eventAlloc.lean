-- Prove2me | Definitions.Def_SybilClinch_Run_eventAlloc
-- name    : SybilClinch_Run_eventAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:46.249636+00:00
-- url     : https://prove2.me/theorems/2c37c5e7-8ac4-462f-a56b-d2c90effb180
-- title:
--   Fixed-price purchases in the event procedure
-- statement:
--   At an event price $p$, with $S$ the post-lump residual supply and $B_A$, $B_E$ the total active and exiting budgets:
--
--   1. if the stopping test (20) holds, every active identity buys $b_i/p$, and every exiting identity buys $\delta_i=\frac{b_i}{B_E}\min\{L,B_E/p\}$ with $L=S-B_A/p$ (21)–(22), after which the run ends;
--   2. otherwise all exiting budgets are cancelled (23), the post-event water level is $h^\star=B_A-pS$, and every active identity with $b_i>h^\star$ buys $(b_i-h^\star)/p$ exactly once (24).
--
--   All purchases are at price $p$.
--
--   **Formalization Note** On every reachable state this quantity is zero at a price with no lump and no exit, so it is applied at every clock price.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, (20)–(24), pp.11–12 (PDF pp.13–14)

import Mathlib
import Definitions.Def_SybilClinch_Run_preActive
import Definitions.Def_SybilClinch_Run_preExit
import Definitions.Def_SybilClinch_Run_preResid

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, (20)–(24), printed pp.11–12 (PDF pp.13–14): the quantity that identity `i` buys at
the fixed price `p` in the event procedure at `p`.

With `S` the post-lump residual supply, `B_A` and `B_E` the total active and exiting budgets:
* if the stopping test (20) `B_A/p ≤ S` holds, every active identity buys `bᵢ/p`, and every
  exiting identity buys `δᵢ = (bᵢ/B_E)·min{L, B_E/p}` with `L = S − B_A/p` (21)–(22);
* otherwise the exiting budgets are cancelled (23), `h⋆ = B_A − pS`, and every active identity
  with `bᵢ > h⋆` buys `(bᵢ − h⋆)/p` once (24).

**Formalization Note.** At a price with no lump and no exit this is `0` on every reachable state
(the stopping test fails while some budget is positive, and every active budget is at most `h`);
`IsRun.jump` therefore applies it at every price. -/
noncomputable def Run.eventAlloc (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ)
    (i : ℕ) : ℝ :=
  let A := R.preActive M P p
  let E := R.preExit M P p
  let S := R.preResid M P p
  let BA := ∑ j ∈ A, R.budPre M P j p
  let BE := ∑ j ∈ E, R.budPre M P j p
  if BA / p ≤ S then
    (if i ∈ A then R.budPre M P i p / p
      else if i ∈ E then R.budPre M P i p / BE * min (S - BA / p) (BE / p) else 0)
  else
    (if i ∈ A then max (R.budPre M P i p - (BA - p * S)) 0 / p else 0)

end SybilClinch


