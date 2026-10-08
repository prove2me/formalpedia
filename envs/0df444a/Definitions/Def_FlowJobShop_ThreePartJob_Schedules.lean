-- Prove2me | Definitions.Def_FlowJobShop_ThreePartJob_Schedules
-- name    : FlowJobShop_ThreePartJob_Schedules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:17:08.000556+00:00
-- url     : https://prove2.me/theorems/c8a9b5bc-f4c6-4421-911e-b3fcff326287
-- title:
--   Finite-piece preemptive schedules and finish-time bounds for Lemma 7
-- statement:
--   A **preemptive schedule** assigns each operation a finite collection of positive-length processing pieces. Each piece has a start and finish time, lies on its operation's assigned machine, and starts at or after time zero. Pieces on one machine occupy disjoint half-open intervals. For each operation, the pieces' lengths sum to its processing time. Every piece of an earlier operation of a job finishes before any piece of a later operation of that job begins. The schedule finishes by time $\tau$ when every piece ends by $\tau$.
--
--   A **non-preemptive schedule** assigns one start time to each operation and satisfies the published job-shop feasibility conditions: nonnegative starts, job precedence, and machine disjointness. It finishes by $\tau$ when every operation ends by $\tau$.
--
--   These are the two schedule classes compared by Lemma 7. The definition permits zero-duration operations to have no preemptive pieces; all operations of the constructed instance have positive duration whenever they exist and the 3-PARTITION input is valid.
--
--   **Formalization Note** The non-preemptive feasibility predicate is reused from `JobShopLTAS.Core.Instance`; the finite-piece preemptive predicate is local to this mission.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), pp. 36, 40 (footnote 1), 44–45, https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartJob_Instance

namespace FlowJobShop.ThreePartJob

/-- A finite preemptive schedule of every operation of a job-shop instance.
Piece `u` processes `op u` during `[start u, finish u)`. Positive-length
pieces on a machine are disjoint; their lengths sum to the operation's
processing time; all pieces of an earlier operation finish before any piece
of a later operation of the same job starts. -/
structure PreemptiveSchedule {m n : ℕ} (inst : JobShopLTAS.Core.Instance m n) where
  pieceCount : ℕ
  op : Fin pieceCount → inst.Op
  start : Fin pieceCount → ℝ
  finish : Fin pieceCount → ℝ
  piece_positive : ∀ u, 0 ≤ start u ∧ start u < finish u
  machine_disjoint : ∀ u v, u ≠ v → inst.mach (op u) = inst.mach (op v) →
    finish u ≤ start v ∨ finish v ≤ start u
  work : ∀ o : inst.Op,
    ∑ u ∈ Finset.univ.filter (fun u => op u = o), (finish u - start u) = inst.proc o
  precedence : ∀ u v, (op u).1 = (op v).1 → (op u).2.val < (op v).2.val →
    finish u ≤ start v

/-- The schedule finishes by `τ` when every piece ends by `τ`. There are no
pieces for zero-length operations, whose completion inherits the end of the
previous operation; this is immaterial to the bound because the previous
piece is included. -/
def PreemptiveSchedule.FinishesBy {m n : ℕ} {inst : JobShopLTAS.Core.Instance m n}
    (S : PreemptiveSchedule inst) (τ : ℝ) : Prop := ∀ u, S.finish u ≤ τ

/-- The published nonpreemptive schedule is feasible and all operations
complete by `τ`. -/
def NonpreemptiveFinishesBy {m n : ℕ} (inst : JobShopLTAS.Core.Instance m n)
    (s : inst.Op → ℝ) (τ : ℝ) : Prop :=
  inst.IsFeasibleSchedule Finset.univ s ∧ ∀ o : inst.Op, s o + inst.proc o ≤ τ

end FlowJobShop.ThreePartJob


