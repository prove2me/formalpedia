-- Prove2me | Definitions.Def_TwoAgentSched_cpAlgo
-- name    : TwoAgentSched_cpAlgo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:48:11.944626+00:00
-- url     : https://prove2.me/theorems/fbf79d95-fc75-427a-b67c-beae8022760b
-- title:
--   The §4 algorithm for $1\|f^A_{\max}:f^B_{\max}$
-- statement:
--   The algorithm of §4 for problem CP with $f^A_{\max}$ and $f^B_{\max}$, as a timed computation. Its input is the processing times $p$, agent $A$'s cost functions $f^A_h$ and agent $B$'s deadlines $D^B_k$ (cuts, see `IsDeadline`); it sees agent $B$ only through the deadlines.
--
--   1. Build the index lists and compute $\bar\tau = \sum_j p_j$.
--   2. Sort the B-jobs by deadline (`sortC`), so that the unscheduled B-job with the largest deadline is on top of a stack.
--   3. Repeat, fixing the job that ends at $\bar\tau$ (the last of the unscheduled jobs):
--      - if the B-job $k$ on top has $(\bar\tau,\mathrm{true}) \le D^B_k$, that is $f^B_k(\bar\tau)\le Q$, schedule it last;
--      - otherwise, if no A-job is left, stop: the answer is the schedule built so far if no B-job is left either, and **infeasible** otherwise;
--      - otherwise scan the unscheduled A-jobs (`scanA`), evaluating $f^A_h(\bar\tau)$ for each, and schedule last the first one with minimum value;
--
--      then decrease $\bar\tau$ by the processing time of the job just scheduled.
--
--   The output is the sequence of all jobs in processing order, or `none` for an infeasible instance.
--
--   **Formalization Note** `argminC`, `scanA`, `cpLoop` and `cpAlgo` are separate definitions; every comparison, evaluation, lookup, subtraction and list step costs one unit. The B-jobs are sorted in nondecreasing order of the reversed order on deadlines (`OrderDual`), so the largest deadline comes first. The loop runs with fuel $n_A+n_B+1$, enough for one step per job plus the final test. The algorithm is generic in the number type (instantiated at `ℝ` in the theorems).
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, pp. 232–233 (the sketch on p. 232 and its refinement on p. 233: deadlines, sorting J^B, largest D^B_k, the A-scan)

import Mathlib
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_sortC

namespace TwoAgentSched

variable {nA nB : ℕ} {R : Type} [LinearOrder R]

/-- The first A-job of the list minimizing `f^A_h(τ̄)`, with that value: one step per cell, one
per evaluation `f^A_h(τ̄)`, one per comparison. `none` on the empty list. -/
def argminC (fA : Fin nA → R → R) (τ : R) : List (Fin nA) → Timed (Option (Fin nA × R))
  | [] => pure none
  | h :: hs => do
      tick
      let v ← evalC (fA h) τ
      let r ← argminC fA τ hs
      match r with
      | none => pure (some (h, v))
      | some (h', v') => do
          let b ← leC v v'
          if b then pure (some (h, v)) else pure (some (h', v'))

/-- **The A-scan** (p. 233: "all unscheduled A-jobs may have to be tried out"): find the first
unscheduled A-job `h*` minimizing `f^A_h(τ̄)` and remove it from the list of unscheduled A-jobs.
`none` on the empty list. -/
def scanA (fA : Fin nA → R → R) (τ : R) (As : List (Fin nA)) :
    Timed (Option (Fin nA × List (Fin nA))) := do
  let r ← argminC fA τ As
  match r with
  | none => pure none
  | some (h, _) => do
      let rest ← eraseC h As
      pure (some (h, rest))

/-- **The main loop of the §4 algorithm** (pp. 232–233). State: fuel, `τ̄` (the total
processing time of the unscheduled jobs), the unscheduled A-jobs `As`, the unscheduled B-jobs
`Bs` as a stack with the largest deadline on top, and the jobs fixed so far `acc`, in processing
order (each fixed job is put in front: it is last among the unscheduled ones). One step:
* if the top B-job `k` has `(τ̄, true) ≤ D k` (one lookup and one comparison), i.e.
  `f^B_k(τ̄) ≤ Q`, it is scheduled to end at `τ̄`;
* otherwise, if no A-job is left, return `some acc` if no B-job is left either, and `none`
  ("the instance is not feasible") otherwise;
* otherwise the A-scan picks the first A-job `h*` minimizing `f^A_h(τ̄)`, which is scheduled to
  end at `τ̄`.
`τ̄` is decreased by the processing time of the job just fixed (one subtraction). The algorithm
sees agent B only through the deadlines `D`. -/
def cpLoop [Sub R] (p : Job nA nB → R) (fA : Fin nA → R → R) (D : Fin nB → WithTop (R ×ₗ Bool)) :
    ℕ → R → List (Fin nA) → List (Fin nB) → List (Job nA nB) →
      Timed (Option (List (Job nA nB)))
  | 0, _, _, _, _ => pure none
  | fuel + 1, τ, As, Bs, acc => do
      let top ← (match Bs with
        | [] => pure none
        | k :: Bs' => do
            let d ← lookupC D k
            let ok ← leC ((toLex (τ, true) : R ×ₗ Bool) : WithTop (R ×ₗ Bool)) d
            pure (if ok then some (k, Bs') else none) : Timed (Option (Fin nB × List (Fin nB))))
      match top with
      | some (k, Bs') => do
          let τ' ← subC τ (p (Sum.inr k))
          tick
          cpLoop p fA D fuel τ' As Bs' (Sum.inr k :: acc)
      | none =>
          match As with
          | [] => pure (match Bs with
              | [] => some acc
              | _ :: _ => none)
          | _ :: _ => do
              let r ← scanA fA τ As
              match r with
              | none => pure none
              | some (h, As') => do
                  let τ' ← subC τ (p (Sum.inl h))
                  tick
                  cpLoop p fA D fuel τ' As' Bs (Sum.inl h :: acc)

/-- **The algorithm of §4 for `1‖f^A_max : f^B_max`** (Agnetis–Mirchandani–Pacciarelli–Pacifici,
Oper. Res. 52(2) (2004), pp. 232–233), inside `Timed`. Input: processing times `p`, agent A's
cost functions `fA`, and agent B's deadlines `D` (cuts, see `IsDeadline`); it does not see
`f^B` or `Q` otherwise. Steps:
1. build the index lists (`2(n_A + n_B)` steps) and compute `τ̄ = ∑_j p_j` (one step per addition);
2. sort the B-jobs by deadline with `sortC` (largest deadline first, i.e. nondecreasing for the
   reversed order, so the stack has the largest deadline on top); each comparison of two
   deadlines, lookups included, is one step;
3. run `cpLoop` with fuel `n_A + n_B + 1` from `acc = []`.
Returns `some σ` (the jobs in processing order) or `none` (infeasible). -/
def cpAlgo [Add R] [Zero R] [Sub R] (p : Job nA nB → R) (fA : Fin nA → R → R)
    (D : Fin nB → WithTop (R ×ₗ Bool)) : Timed (Option (List (Job nA nB))) := do
  ticks (2 * (nA + nB))
  let As := List.finRange nA
  let Bs0 := List.finRange nB
  let τ ← sumC p (As.map Sum.inl ++ Bs0.map Sum.inr)
  let Bs ← sortC (fun k => OrderDual.toDual (D k)) Bs0
  cpLoop p fA D (nA + nB + 1) τ As Bs []

end TwoAgentSched


