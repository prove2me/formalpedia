-- Prove2me | Definitions.Def_GreedyReusableNet_coupledRun
-- name    : GreedyReusableNet_coupledRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:52.237628+00:00
-- url     : https://prove2.me/theorems/89d59454-1802-463a-9472-9c1902950b32
-- title:
--   The queue coupling of a policy $\pi$ and OPT
-- statement:
--   The **queue coupling** runs a policy $\pi$ and a benchmark OPT on one probability space, period by period, $\pi$ first:
--
--   1. $\pi$ runs its period with its own seeds; for every arm $i$ of a bundle it activates, its uniform seed $U_{t,i}$, which gave its blocking time $F_i^{-1}(U_{t,i};n^\pi_{t,i})$, is appended to a FIFO queue $Q_i$;
--   2. OPT takes its action and draws its activations with its own seeds; for every arm $i$ of a bundle it activates, the front seed $U_{t',i}$ of $Q_i$ is removed and OPT's blocking time is $F_i^{-1}(U_{t',i};n^{\mathrm{OPT}}_{t,i})$; if $Q_i$ is empty, a fresh uniform seed of OPT is used.
--
--   The coupling space carries the initial seeds and tapes of both policies, independent. $\pi$'s history in the coupled run is its history in its own run. The module records the seeds OPT used.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.2, Queue Coupling, p.20

import Mathlib
import Definitions.Def_GreedyReusableNet_run
import Definitions.Def_GreedyReusableNet_Rule

open MeasureTheory

namespace GreedyReusableNet

/-- **The state of the queue coupling**: the history of the policy `π`, the history of the
benchmark OPT, the FIFO queue `Q_i` of uniform seeds of each arm, and the record of the seeds OPT
used for its times `b_{t,i}` in each period. -/
abbrev CoupledState (N : ℕ) := History N × History N × (Fin N → List ℝ) × List (Fin N → ℝ)

/-- **One period of the queue coupling** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §3.2, "Queue
Coupling", p.20). In period `t`, first `π`, then OPT ("we go through time period from 1 to `T`
and consider `π` and OPT in turn"):

* `π` runs one period of Algorithm 1 (`stepOf`) with its own seeds `wP`; for every arm `i` of a
  bundle it activated, its uniform seed `U_{t,i}` (used for its blocking time
  `F_i^{-1}(U_{t,i}; n^π_{t,i})`) is inserted at the rear of the queue `Q_i`;
* OPT takes its action and draws its activated bundles with its own seeds `wO`; for every arm `i`
  of a bundle it activated, the first seed of `Q_i` is popped and used for OPT's blocking time
  `F_i^{-1}(U_{t',i}; n^OPT_{t,i})`; if `Q_i` is empty, OPT's own fresh seed `U_{t,i}` (from `wO`)
  is used. The seeds OPT used are recorded (`0` for arms it did not activate). -/
noncomputable def coupledStep {N : ℕ} (I : ProblemInstance N) (t : ℕ)
    (actP actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (c : CoupledState N)
    (wP wO : Noise N) : CoupledState N := by
  classical
  let h := c.1
  let h' := c.2.1
  let Q := c.2.2.1
  let stP := stepOf I t h (actP t h wP.1) wP.2.1 wP.2.2
  let Q1 : Fin N → List ℝ := fun i =>
    if i ∈ activatedArms stP.2.1 then Q i ++ [wP.2.2 i] else Q i
  let S' := sampleFin ((I.period t).act
    (takenAction (I.period t) (freeArms h' t) (actO t h' wO.1)) (counts h')) wO.2.1
  let seedO : Fin N → ℝ := fun i =>
    if i ∈ activatedArms S' then (Q1 i).headD (wO.2.2 i) else 0
  let Q2 : Fin N → List ℝ := fun i => if i ∈ activatedArms S' then (Q1 i).tail else Q1 i
  let stO := stepOf I t h' (actO t h' wO.1) wO.2.1 seedO
  exact (h ++ [stP], h' ++ [stO], Q2, c.2.2.2 ++ [seedO])

/-- **The queue-coupled run** of a policy `π` (decision rule `actP`, seeds `w`) and a benchmark
OPT (decision rule `actO`, seeds `w'`) over the horizon `T`, from empty histories and empty
queues (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §3.2, p.20). `π`'s history in the coupled run is
exactly its history `run I actP w` in its own run. -/
noncomputable def coupledRun {N T : ℕ} (I : ProblemInstance N)
    (actP actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w w' : Tape N T) :
    ℕ → CoupledState N
  | 0 => ([], [], fun _ => [], [])
  | t + 1 =>
    if ht : t < T then
      coupledStep I t actP actO (coupledRun I actP actO w w' t) (w ⟨t, ht⟩) (w' ⟨t, ht⟩)
    else coupledRun I actP actO w w' t

/-- **The coupling probability space** of two policies: the initial seed and the tape of `π`, and
independently the initial seed and the tape of OPT. -/
noncomputable def coupledLaw {N : ℕ} (T : ℕ) (π π' : Rule N) :
    Measure ((ℝ × Tape N T) × (ℝ × Tape N T)) :=
  (π.seedLaw.prod (tapeLaw N T)).prod (π'.seedLaw.prod (tapeLaw N T))

/-- The final state of the queue-coupled run of `π` and OPT `π'` at the sample point
`x = ((s, w), (s', w'))`. -/
noncomputable def coupledFinal {N : ℕ} (I : ProblemInstance N) (T : ℕ) (π π' : Rule N)
    (x : (ℝ × Tape N T) × (ℝ × Tape N T)) : CoupledState N :=
  coupledRun I (π.act x.1.1) (π'.act x.2.1) x.1.2 x.2.2 T

end GreedyReusableNet


