-- Prove2me | Definitions.Def_TwoAgentSched_lawler
-- name    : TwoAgentSched_lawler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:47:43.490091+00:00
-- url     : https://prove2.me/theorems/f1bb137e-873c-4559-a9ec-a2a60dc1a0b6
-- title:
--   Lawler's algorithm for $1|prec|f_{\max}$, with its running time
-- statement:
--   **Lawler's rule** for the single-machine problem $1|prec|f_{\max}$: jobs $1,\dots,n$ with processing times $p_j$, nondecreasing cost functions $g_j$ and a precedence relation ($i \to j$: job $i$ must be processed before job $j$). Starting from $\bar\tau = \sum_j p_j$, repeatedly put **last**, among the unscheduled jobs with no unscheduled successor, one with the least $g_j(\bar\tau)$, and decrease $\bar\tau$ by its processing time.
--
--   The timed implementation:
--
--   1. builds the job list and a zero array of successor counts ($2n$ steps), computes $\bar\tau$ (one step per addition) and, for every job, its number of successors ($n^2$ relation queries);
--   2. at each step scans the unscheduled jobs, evaluates $g_j(\bar\tau)$ for those with successor count $0$ and keeps the first one of least value (one step per cell, evaluation and comparison), removes it from the list, decrements the counts of its unscheduled predecessors (one step per job inspected) and updates $\bar\tau$ (one subtraction);
--   3. returns the jobs in processing order, or reports failure if some step finds no job without unscheduled successor (impossible for an acyclic relation).
--
--   **Formalization Note** `lawler p g prec` is generic in the number type of the processing times (instantiated at `ℝ` in the theorems) and in the linear order `β` of the costs; the main loop `lawlerLoop` runs with fuel $n+1$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, p. 232 ("For the latter problem, Lawler (1973) devises an O(n^2) time algorithm")

import Mathlib
import Definitions.Def_TwoAgentSched_Timed

namespace TwoAgentSched

variable {n : ℕ} {R β : Type}

/-- The number of jobs `j ∈ L` with `prec i j` (successors of `i` in `L`): one step per
relation query. -/
def countSuccC (prec : Fin n → Fin n → Prop) [DecidableRel prec] (i : Fin n) :
    List (Fin n) → Timed ℕ
  | [] => pure 0
  | j :: js => do
      tick
      let c ← countSuccC prec i js
      pure (if prec i j then c + 1 else c)

/-- The initial successor counts: for each `i` in the list, the number of its successors in `L`
(`|L|` relation queries per job), stored in an array (one step per write). -/
def initCountsC (prec : Fin n → Fin n → Prop) [DecidableRel prec] (L : List (Fin n)) :
    List (Fin n) → Timed (Fin n → ℕ)
  | [] => pure (fun _ => 0)
  | i :: is => do
      let cnt ← initCountsC prec L is
      let c ← countSuccC prec i L
      tick
      pure (Function.update cnt i c)

/-- After job `j` is scheduled, decrement the successor count of every `i` in the list with
`prec i j`: one step per job inspected (relation query and array write). -/
def decrC (prec : Fin n → Fin n → Prop) [DecidableRel prec] (j : Fin n) :
    List (Fin n) → (Fin n → ℕ) → Timed (Fin n → ℕ)
  | [], cnt => pure cnt
  | i :: is, cnt => do
      tick
      decrC prec j is (if prec i j then Function.update cnt i (cnt i - 1) else cnt)

/-- Among the jobs `j` of the list whose count `cnt j` is `0` (no unscheduled successor), the
first one minimizing `g j τ`, with that value; one step per cell, one per evaluation of `g`, one
per comparison. `none` if no job of the list has count `0`. -/
def argminEligibleC [LinearOrder β] (g : Fin n → R → β) (τ : R) (cnt : Fin n → ℕ) :
    List (Fin n) → Timed (Option (Fin n × β))
  | [] => pure none
  | j :: js => do
      tick
      let r ← argminEligibleC g τ cnt js
      if cnt j = 0 then do
        let v ← evalC (g j) τ
        match r with
        | none => pure (some (j, v))
        | some (j', v') => do
            let b ← leC v v'
            if b then pure (some (j, v)) else pure (some (j', v'))
      else pure r

/-- The main loop of Lawler's rule. State: fuel, `τ̄` (the total processing time of the
unscheduled jobs `U`), the unscheduled jobs `U`, their unscheduled-successor counts `cnt`, and the
jobs fixed so far `acc` in processing order. Each step puts last, among the unscheduled jobs
with no unscheduled successor, the first one with least `g j τ̄`. Returns `none` if some step
finds no such job (impossible for an acyclic relation) or the fuel runs out. -/
def lawlerLoop [LinearOrder β] [Sub R] (p : Fin n → R) (g : Fin n → R → β)
    (prec : Fin n → Fin n → Prop) [DecidableRel prec] :
    ℕ → R → List (Fin n) → (Fin n → ℕ) → List (Fin n) → Timed (Option (List (Fin n)))
  | 0, _, _, _, _ => pure none
  | fuel + 1, τ, U, cnt, acc =>
      match U with
      | [] => pure (some acc)
      | _ :: _ => do
          let r ← argminEligibleC g τ cnt U
          match r with
          | none => pure none
          | some (j, _) => do
              let U' ← eraseC j U
              let cnt' ← decrC prec j U' cnt
              let τ' ← subC τ (p j)
              tick
              lawlerLoop p g prec fuel τ' U' cnt' (j :: acc)

/-- **Lawler's algorithm for `1|prec|f_max`** (Lawler 1973, cited in Agnetis–Mirchandani–
Pacciarelli–Pacifici, Oper. Res. 52(2) (2004), §4, p. 232), inside `Timed`. Jobs `Fin n` with
processing times `p`, nondecreasing costs `g j`, and a precedence relation `prec` (`prec i j`:
`i` must be processed before `j`). It builds the job list and a zero count array (`2n` steps),
computes `τ̄ = ∑ p j`, the successor counts (`n²` queries), and runs `lawlerLoop` with fuel
`n + 1`. The output, when `some σ`, lists the jobs in processing order. -/
def lawler [LinearOrder β] [Add R] [Zero R] [Sub R] (p : Fin n → R) (g : Fin n → R → β)
    (prec : Fin n → Fin n → Prop) [DecidableRel prec] : Timed (Option (List (Fin n))) := do
  ticks (2 * n)
  let U := List.finRange n
  let τ ← sumC p U
  let cnt ← initCountsC prec U U
  lawlerLoop p g prec (n + 1) τ U cnt []

end TwoAgentSched


