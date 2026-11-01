-- Prove2me | Definitions.Def_GreedyReusableNet_run
-- name    : GreedyReusableNet_run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:35.710209+00:00
-- url     : https://prove2.me/theorems/ad88aa3f-59ef-4c03-9b39-427b1c751ce2
-- title:
--   One run of Algorithm 1 for a policy
-- statement:
--   Starting from the empty history, in each period $t<T$:
--
--   1. the policy proposes an action set from its history and its period seed; if the proposal is an available action set of $\mathscr A_t$ it is taken, otherwise the empty action set is taken;
--   2. the activated bundles $\mathcal A_{t,\mathrm{act}}$ are drawn from the activation law of the action taken at the current counting vector $n_t$;
--   3. each arm $i$ of an activated bundle receives the blocking time $F_i^{-1}(U_{t,i};n_{t,i})$ and is blocked during $(t,t+b_{t,i}]$; its count increases by one.
--
--   Rewards $\sum_{B\in\mathcal A_{t,\mathrm{act}}}r_t(B;n_t(B))$ are read from the resulting history. This is Algorithm 1 (pp.8–9) for a fixed sample of the seeds.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Algorithm 1, pp.8–9

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance
import Definitions.Def_GreedyReusableNet_History
import Definitions.Def_GreedyReusableNet_tapeLaw
import Definitions.Def_GreedyReusableNet_sampleFin
import Definitions.Def_GreedyReusableNet_Finv

namespace GreedyReusableNet

/-- **The action set actually taken**: a proposal `A` is taken when it is an available action
set of `𝒜_t` (`IsAvailableSet`), and replaced by the empty action set otherwise (Simchi-Levi,
Zheng & Zhu, SSRN 3981123, Algorithm 1 step 3, p.8: "`π` takes an action `𝒜^π_t ∈ 𝒜_t` such that
any arm in `𝒜^π_t` is available"). Every policy therefore only ever takes available action sets
of `𝒜_t` (`∅ ∈ 𝒜_t` under Assumption 1). -/
noncomputable def takenAction {N : ℕ} (d : PeriodData N) (free : Finset (Fin N))
    (A : Finset (Finset (Fin N))) : Finset (Finset (Fin N)) := by
  classical
  exact if IsAvailableSet d free A then A else ∅

/-- **One period of Algorithm 1** (SSRN 3981123, pp.8–9) for the history `h` at period `t`, the
proposed action set `A`, the activation seed `uAct` and the blocking seeds `U`:

1. the action set taken is `A' = takenAction (period t) (freeArms h t) A` (step 3);
2. the activated bundles `S` are drawn from the activation law `act A' n_t` with the seed `uAct`
   (step 3), where `n_t = counts h` is the counting vector before period `t`;
3. every arm `i` of an activated bundle gets the blocking time `F_i^{-1}(U_i; n_{t,i})` (step 6;
   the quantile sampling of §3.2, p.20); other arms get the unused value `0`.

The rewards (step 4) and the count increments (step 7) are read off the record later
(`pathSum`, `counts`). -/
noncomputable def stepOf {N : ℕ} (I : ProblemInstance N) (t : ℕ) (h : History N)
    (A : Finset (Finset (Fin N))) (uAct : ℝ) (U : Fin N → ℝ) : Step N := by
  classical
  let d := I.period t
  let n := counts h
  let A' := takenAction d (freeArms h t) A
  let S := sampleFin (d.act A' n) uAct
  exact (A', S, fun i => if i ∈ activatedArms S then Finv (I.block i (n i)) (U i) else 0)

/-- **The run of a policy** (Algorithm 1, SSRN 3981123, pp.8–9): starting from the empty history
(all counts `0`, every arm available), in each period `t < T` the policy proposes
`act t h u` from the current history `h` and its period seed `u`, and `stepOf` records the period;
after `T` periods the history is frozen.

**Formalization Note** `act` is the policy's decision rule with its initial seed already fixed
(see `Rule`). Period `t` uses the seeds `w t = (u, uAct, U)` of the tape. -/
noncomputable def run {N T : ℕ} (I : ProblemInstance N)
    (act : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w : Tape N T) : ℕ → History N
  | 0 => []
  | t + 1 =>
    if ht : t < T then
      run I act w t ++
        [stepOf I t (run I act w t) (act t (run I act w t) (w ⟨t, ht⟩).1)
          (w ⟨t, ht⟩).2.1 (w ⟨t, ht⟩).2.2]
    else run I act w t

end GreedyReusableNet


