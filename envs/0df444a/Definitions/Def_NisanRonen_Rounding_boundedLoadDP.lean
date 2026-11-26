-- Prove2me | Definitions.Def_NisanRonen_Rounding_boundedLoadDP
-- name    : NisanRonen_Rounding_boundedLoadDP
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T05:33:18.086246+00:00
-- url     : https://prove2.me/theorems/d4413ce0-8600-5a1d-b66e-a0c518bb0746
-- title:
--   Load-vector dynamic programming for bounded unrelated-machine scheduling
-- statement:
--   Fix the number of machines and a cap on integer processing times. A state stores a vector of machine loads and one allocation of the processed jobs that realizes those loads. Starting from all-zero loads, the dynamic program tries every machine for each new job and retains one witness per distinct resulting load vector. It then returns a witness whose maximum machine load is smallest. If an input entry exceeds the cap, the program returns the empty list.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. A concrete load-vector implementation of the exact dynamic-programming step on the rounded instance.

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Lattice.Fold

namespace NisanRonen.Rounding

/-- A state records the integer loads together with an allocation realizing them. -/
abbrev LoadState (n : ℕ) := (Fin n → ℕ) × List (Fin n)

/-- Prepend one job to the allocation and add its processing time to its chosen agent. -/
def prependJob {n : ℕ} (column : Fin n → ℕ) (state : LoadState n) (agent : Fin n) :
    LoadState n :=
  (fun i => (if i = agent then column i else 0) + state.1 i, agent :: state.2)

/-- Retain one allocation for each distinct vector of loads. -/
def keepLoadStates {n : ℕ} (states : List (LoadState n)) : List (LoadState n) :=
  states.eraseDupsBy fun a b => decide (a.1 = b.1)

/-- Enumerate reachable load vectors from the end of the job list, keeping one witness each. -/
def loadStates {n : ℕ} : List (Fin n → ℕ) → List (LoadState n)
  | [] => [(fun _ => 0, [])]
  | column :: columns =>
      keepLoadStates ((loadStates columns).flatMap fun state =>
        (List.finRange n).map (prependJob column state))

/-- Return a minimum-makespan allocation for processing times at most the fixed cap.
The empty output on entries above the cap makes the program total on arbitrary input. -/
def boundedLoadDP {n : ℕ} (cap : ℕ) (columns : List (Fin n → ℕ)) : List (Fin n) :=
  if columns.all (fun column => (List.finRange n).all (fun i => decide (column i ≤ cap))) then
    (((loadStates columns).argmin (fun state => Finset.univ.sup state.1)).map Prod.snd).getD []
  else
    []

end NisanRonen.Rounding


