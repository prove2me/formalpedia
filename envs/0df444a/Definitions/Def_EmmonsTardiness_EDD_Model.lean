-- Prove2me | Definitions.Def_EmmonsTardiness_EDD_Model
-- name    : EmmonsTardiness_EDD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:28:09.328985+00:00
-- url     : https://prove2.me/theorems/b451636e-6e5f-423c-95c3-c24f247b3dd7
-- title:
--   The penalty Σ_J g(T_i), optimal schedules for it, starting times W_i and EDD order
-- statement:
--   This file sets up the one-machine model of Emmons (1969). A finite set $J$ of jobs is processed on one machine; job $J_i$ has a processing time $p_i$ and a due date $d_i$ (real numbers). All jobs are available at time $0$. A **schedule** of $J$ is an ordering of its jobs; the machine starts at time $0$ and processes the jobs one after another without idle time, so the **completion time** $C_i$ of $J_i$ is the sum of the processing times of $J_i$ and of all jobs before it (Moore's `completionTime`, imported).
--
--   The tardiness $T_i = \max(0, C_i - d_i)$ of $J_i$, the relation "$J_a$ precedes $J_b$ in $l$" ($J_a$ occupies an earlier position than $J_b$) and the indexing convention of p. 703 ($j<k$ implies $p_j<p_k$, or $p_j = p_k$ and $d_j\le d_k$) are imported from the shared model of this paper (`EmmonsTardiness.SPT.Model`). For a schedule $l$ of $J$ this file defines:
--
--   1. for a loss function $g:\mathbb R\to\mathbb R$, the **objective**
--   $$\Phi_g(l) = \sum_{i\in J} g(T_i),$$
--   which for $g(T) = T$ is the total tardiness $T = \sum_J T_i$;
--   2. **optimality**: $l$ is optimal for $g$ if it is a schedule of $J$ and $\Phi_g(l)\le\Phi_g(l')$ for every schedule $l'$ of $J$;
--   3. the **waiting (starting) time** $W_i = C_i - p_i$;
--   4. **EDD order**: due dates are nondecreasing along $l$ (ties in any order).
--
--   These are the objects every statement of the mission is about: the theorems compare $\Phi_g$ over all schedules of $J$, and the statements "$j\leftarrow k$" ("$J_j$ precedes $J_k$ in an optimal schedule") are expressed through optimality and precedence.
--
--   **Formalization Note** Jobs are elements of a type $\iota$; where the paper's index matters, $\iota$ carries a linear order which is the paper's job index, and the job set is a finite set $J\subseteq\iota$. A schedule is a duplicate-free list whose elements are exactly $J$ (Moore's `IsSchedule`), positions are $0$-based, and Moore's completion time is applied with Emmons's $p$ in the place of Moore's $t$. Precedence compares list positions (`List.idxOf`).
-- source:
--   Emmons, One-Machine Sequencing to Minimize Certain Functions of Job Tardiness, Operations Research 17(4), 1969, p. 701 (model, lateness, tardiness), p. 702 (optimal schedule), p. 703 (notation j←k, indexing convention), p. 706 (waiting times W_i, Corollary 2.2), p. 713 (objective Σ_J g(T_i))

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.EDD

open MooreLateJobs

/-- The objective `Σ_J g(T_i)` of p. 713: the sum over the job set `J` of the common loss
function `g` applied to each job's tardiness `EmmonsTardiness.SPT.tardiness p d l i` in the
sequence `l`. With `g = id` it is the total tardiness `T = Σ_J T_i` of p. 701. -/
noncomputable def totalPenalty {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι) (l : List ι) : ℝ :=
  ∑ i ∈ J, g (EmmonsTardiness.SPT.tardiness p d l i)

/-- `l` is an optimal schedule of `J` for the objective `Σ_J g(T_i)`: it is a schedule of `J`
and no schedule of `J` has a smaller objective value. -/
def IsOptimal {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ) (J : Finset ι)
    (l : List ι) : Prop :=
  Shared.IsSchedule J l ∧
    ∀ l' : List ι, Shared.IsSchedule J l' → totalPenalty g p d J l ≤ totalPenalty g p d J l'

/-- The waiting (or starting) time `W_i = C_i - p_i` of job `i` in the sequence `l`
(p. 706, Corollary 2.2). -/
noncomputable def startTime {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (l : List ι) (i : ι) : ℝ :=
  Shared.completionTime p l i - p i

/-- The sequence `l` is in EDD (earliest due date) order: due dates are nondecreasing along `l`.
Ties between equal due dates may be broken arbitrarily. -/
def IsEDDOrder {ι : Type*} (d : ι → ℝ) (l : List ι) : Prop :=
  l.Pairwise (fun a b => d a ≤ d b)

end EmmonsTardiness.EDD


