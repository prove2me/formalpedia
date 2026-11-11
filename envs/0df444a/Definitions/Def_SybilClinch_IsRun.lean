-- Prove2me | Definitions.Def_SybilClinch_IsRun
-- name    : SybilClinch_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:43:48.087304+00:00
-- url     : https://prove2.me/theorems/b7a10176-d915-4e3d-83b0-362296fe0bd1
-- title:
--   Completed run of a target-based clinching auction
-- statement:
--   A completed run of the target-based clinching mechanism (the §3 mechanism with $(p_0,T^{\rm amm},x_0)$ replaced by $(p_\star,T,X_\sigma)$, (29)) on a one-sided profile consists of a terminal price $p_f\ge p_\star$ and allocation paths such that:
--
--   1. allocations are zero before $p_\star$, constant from $p_f$ on, and zero for labels outside the profile;
--   2. at every clock price $p\in[p_\star,p_f]$ the jump of each allocation is the quantity bought in the event procedure at $p$ (lump first, then the stopping test, then the stopping allocation, or the cancellation of exiting budgets followed by one-shot restoration);
--   3. an identity outside Clinch does not trade continuously (17), and an identity in Clinch stays at the water level $b_i=h$ as the clock rises, while it is active (18); trade is charged at the clock price and budgets decrease by payments;
--   4. the run continues at every price of $[p_\star,p_f)$ and ends at $p_f$; reaching capacity does not end it (zero-trade completion).
--
--   **Formalization Note** The primitive conditions (16)–(18) are imposed in integrated form: the continuous part of $dx_i$ has no mass where $i$ is not clinching, and a clincher stays tight on a right neighbourhood of each price. No trading-rate formula (Lemma 4.4) and no absolute continuity of the paths is assumed: event prices may accumulate, and for some admissible AMMs the sole-survivor path is continuous but singular. Values may be $+\infty$ (the identity never exits).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2–§3.5, pp.9–12 (PDF pp.11–14); §4.1, (29) and the completion convention, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_SybilClinch_Run_eventAlloc
import Definitions.Def_SybilClinch_Run_clinch
import Definitions.Def_SybilClinch_Run_Terminates

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2–§3.5, printed pp.9–12 (PDF pp.11–14), with the substitution (29) of §4.1, printed
p.14 (PDF p.16): `R` is a completed run of the target-based clinching mechanism `M` on the one-sided
profile `P`.

* The clock starts at `p⋆` (10) and ends at `p_f ≥ p⋆`; allocations are zero before `p⋆`, constant
  from `p_f` on, and zero for labels outside the profile.
* Events (§3.4): at every clock price `p ∈ [p⋆, p_f]` the jump of each allocation equals the
  quantity bought in the event procedure (lump first, then the stopping test, then the stopping
  allocation, or cancellation of exiting budgets and one-shot restoration).
* Continuous evolution (§3.3, (16)–(18)): an identity outside `Clinch` does not trade (the
  continuous part of `dxᵢ` vanishes off `Clinch`), and an identity in `Clinch` remains tight at the
  water level (`bᵢ = h`) as the clock rises, while it stays active. Trade is charged at the clock
  price and budgets decrease by payments (built into `Run.pay`, `Run.bud`).
* Continuation and termination (§3.5): the run continues at every `p ∈ [p⋆, p_f)` and ends at
  `p_f`. Reaching capacity does not terminate the run (zero-trade completion, p.14).

**Formalization Note.** The primitive conditions (16)–(18) are imposed in integrated form: the
continuous part of `dxᵢ` (its restriction to continuity points of `xᵢ`) has no mass where `i` is
not clinching, and a clincher stays at the water level on a right neighbourhood of each price
while it is active. No trading-rate formula (Lemma 4.4) and no absolute-continuity requirement on
the paths is built in. Values may be `+∞` (never exits). -/
structure IsRun (M : TargetMech) (P : OneSidedProfile) (R : Run) : Prop where
  start_le : M.pstar ≤ R.pf
  zero_before : ∀ i p, p < M.pstar → R.x i p = 0
  const_after : ∀ i p, R.pf ≤ p → R.x i p = R.x i R.pf
  zero_outside : ∀ i, i ∉ P.ids → ∀ p, R.x i p = 0
  jump : ∀ i ∈ P.ids, ∀ p ∈ Icc M.pstar R.pf,
    R.x i p - Function.leftLim (R.x i) p = R.eventAlloc M P p i
  no_trade_off_clinch : ∀ i ∈ P.ids,
    (R.x i).measure {p | p ∈ Ioo M.pstar R.pf ∧ ContinuousAt (R.x i) p ∧ i ∉ R.clinch M P p} = 0
  tight : ∀ i ∈ P.ids, ∀ p ∈ Ico M.pstar R.pf, i ∈ R.clinch M P p →
    ∃ ε > 0, ∀ p' ∈ Ioo p (p + ε), p' < R.pf → (p' : WithTop ℝ) < P.v i →
      0 < R.bud M P i p' → R.bud M P i p' = R.waterLevel M P p'
  continuing : ∀ p ∈ Ico M.pstar R.pf, ¬ R.Terminates M P p
  terminal : R.Terminates M P R.pf

end SybilClinch


