-- Prove2me | Definitions.Def_WilliamsonShmoys_ParallelMakespan
-- name    : WilliamsonShmoys_ParallelMakespan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T08:00:00.602158+00:00
-- url     : https://prove2.me/theorems/d9b8a3b3-7c92-43f3-b523-95b4df297537
-- title:
--   Identical-machine makespan and positive integer PTAS instances
-- statement:
--   Total processing time assigned to each machine; maximum machine load; positive integer job processing requirements and a positive input machine count encoded as predecessor naturals; exact real-valued times and binary input encoding. The natural-list binary encoder is imported from the earlier book package.
-- source:
--   Williamson and Shmoys, The Design of Approximation Algorithms, author electronic manuscript, Theorem 3.7, p. 72; §3.2 pp. 69–72 (Cambridge University Press, 2011), https://doi.org/10.1017/CBO9780511921735

import Definitions.Def_WilliamsonShmoys_SetCoverFrequency
import Mathlib.Order.Filter.Extr

set_option autoImplicit false
open scoped BigOperators
namespace WilliamsonShmoys

/-- Total processing time assigned to a machine: the equivalent load-balancing
model of §2.3, manuscript pp.39–40. An assignment processes every job exactly once. -/
noncomputable def machineLoad {n m : ℕ} (p : Fin n → ℝ)
    (assignment : Fin n → Fin m) (machine : Fin m) : ℝ :=
  ∑ j : Fin n, if assignment j = machine then p j else 0

/-- Maximum machine load; the branch for no machines only makes the definition
 total. The main statement explicitly requires a positive number of machines. -/
noncomputable def makespan {n m : ℕ} (p : Fin n → ℝ)
    (assignment : Fin n → Fin m) : ℝ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.sup' h (machineLoad p assignment)
  else 0

/-- The positive integer instances of §3.2, manuscript p.69. Predecessors
encode positive processing times and a positive, variable machine count.
The empty job list is also allowed, with makespan zero. -/
structure ParallelPTASInput where
  machinesPred : ℕ
  processingPred : List ℕ

/-- Exact integral processing requirements, embedded into the existing
real-valued identical-machine objective. No rounding is part of the instance. -/
def parallelPTASTimes (I : ParallelPTASInput)
    (j : Fin I.processingPred.length) : ℝ :=
  ((I.processingPred.get j + 1 : ℕ) : ℝ)

/-- Binary positive machine count followed by binary positive job times,
using the existing comma-delimited encoder. No unary padding or solution data. -/
def parallelPTASEncodeInput (I : ParallelPTASInput) : List Computability.Γ' :=
  lptEncodeNaturals ((I.machinesPred + 1) :: I.processingPred.map (· + 1))

end WilliamsonShmoys


