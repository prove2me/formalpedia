-- Prove2me | Definitions.Def_UnrelatedSched_FixedMachines_BinarySearch
-- name    : UnrelatedSched_FixedMachines_BinarySearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:31.829972+00:00
-- url     : https://prove2.me/theorems/d03d4581-0603-4a61-a3e6-b5bfdd4ac35a
-- title:
--   ρ-relaxed decision procedures and the binary search of Lemma 1
-- statement:
--   Fix a matrix $P$ of positive integer processing times, $m\ge 1$ machines and $n$ jobs. A **decision procedure** maps each integer deadline $d$ to one of two answers: 'no', or 'almost' together with a schedule. For $\rho\ge 1$ it is **$\rho$-relaxed** when, on every input $d$,
--
--   1. it either outputs 'no' or produces a schedule with makespan at most $\rho d$, and
--   2. if the output is 'no', then there is no schedule with makespan at most $d$.
--
--   The **binary search** of the proof of Lemma 1 turns a decision procedure into a schedule. It starts from the **greedy schedule**, in which each job is assigned to a machine on which it runs fastest (ties broken by the smallest machine index). If the makespan of the greedy schedule is $t$, the initial bounds are $u=t$ and $l=\lceil t/m\rceil$. While $l<u$ it sets $d=\lfloor (u+l)/2\rfloor$ and runs the procedure on $d$: on 'almost' with a schedule $\sigma$ it resets $u$ to $d$ and stores the better of $\sigma$ and the schedule stored so far; on 'no' it resets $l$ to $d+1$. When the bounds meet it outputs the stored schedule, which is the best solution found (the greedy schedule if the procedure never answered 'almost').
--
--   Lemma 1 of the paper says that a polynomial $\rho$-relaxed decision procedure yields a polynomial $\rho$-approximation algorithm via this search.
--
--   **Formalization Note** A procedure is a map `ℕ → Option (Fin n → Fin m)`, with `none` for 'no'. The paper's lower bound $t/m$ is rounded up to $\lceil t/m\rceil$ because every makespan is an integer. "The best solution" is the stored schedule of smallest makespan; when the new schedule ties with the stored one, the new one is kept. The loop terminates by recursion on $u-l$. Load and makespan are those of the published definition `MatousekLP.Scheduling.Schedule`.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 5, Section 3, definition of a ρ-relaxed decision procedure and proof of Lemma 1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.FixedMachines

open MatousekLP.Scheduling

/-- A *ρ-relaxed decision procedure* (§3, p. 5). For a fixed matrix `P` of processing times a
procedure is a map `D : ℕ → Option (Fin n → Fin m)` from deadlines to answers: `none` is 'no',
`some σ` is 'almost' together with the schedule `σ`. It is ρ-relaxed when, on every input `d`,
(1) it either outputs 'no' or produces a schedule with makespan at most `ρ d`, and
(2) if the output is 'no', then there is no schedule with makespan at most `d`. -/
def IsRelaxedDecisionProcedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ρ : ℝ)
    (D : ℕ → Option (Fin n → Fin m)) : Prop :=
  ∀ d : ℕ,
    (∀ σ, D d = some σ → makespan (fun i j => (P i j : ℝ)) σ ≤ ρ * (d : ℝ)) ∧
    (D d = none → ∀ τ : Fin n → Fin m, (d : ℝ) < makespan (fun i j => (P i j : ℝ)) τ)

/-- The machine on which job `j` runs fastest (proof of Lemma 1, p. 5); ties are broken by the
smallest machine index. Requires at least one machine. -/
noncomputable def fastestMachine {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ)
    (j : Fin n) : Fin m :=
  (Finset.univ.filter (fun i : Fin m => ∀ i', P i j ≤ P i' j)).min' (by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i : Fin m => P i j)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i' => hi i' (Finset.mem_univ _)⟩⟩)

/-- The greedy schedule of the proof of Lemma 1 (p. 5): each job is assigned to the machine on
which it runs fastest. -/
noncomputable def greedySchedule {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) :
    Fin n → Fin m :=
  fun j => fastestMachine hm P j

/-- The binary-search loop of the proof of Lemma 1 (p. 5). With current lower bound `l`, upper
bound `u` and stored schedule `best`: while `l < u`, set `d = ⌊(u + l)/2⌋` and run `D` on `d`;
on 'almost' with `σ` reset `u` to `d` and keep the better (smaller makespan) of `σ` and `best`,
on 'no' reset `l` to `d + 1`. When `l = u` (or `l > u`) output the stored schedule. -/
noncomputable def searchLoop {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (D : ℕ → Option (Fin n → Fin m)) (l u : ℕ) (best : Fin n → Fin m) : Fin n → Fin m :=
  if _h : l < u then
    match D ((u + l) / 2) with
    | some σ =>
      searchLoop P D l ((u + l) / 2)
        (if makespan (fun i j => (P i j : ℝ)) σ ≤ makespan (fun i j => (P i j : ℝ)) best
          then σ else best)
    | none => searchLoop P D ((u + l) / 2 + 1) u best
  else best
termination_by u - l
decreasing_by all_goals omega

/-- The algorithm of Lemma 1 (p. 5) built on the decision procedure `D`: start from the greedy
schedule, whose makespan `t` is the initial upper bound `u`; the initial lower bound is
`l = ⌈t / m⌉` (the paper's lower bound `t / m`, rounded up because every makespan is an
integer); run the binary search and output the best schedule found. -/
noncomputable def binarySearch {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ)
    (D : ℕ → Option (Fin n → Fin m)) : Fin n → Fin m :=
  searchLoop P D ⌈((UnrelatedSched.TwoApprox.natMakespan P (greedySchedule hm P) : ℕ) : ℝ) / (m : ℝ)⌉₊
    (UnrelatedSched.TwoApprox.natMakespan P (greedySchedule hm P)) (greedySchedule hm P)

end UnrelatedSched.FixedMachines


