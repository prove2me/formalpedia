-- Prove2me | Definitions.Def_GrahamAnomaly_KLongest_Model
-- name    : GrahamAnomaly_KLongest_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:28:46.436808+00:00
-- url     : https://prove2.me/theorems/99e6d920-6cec-4276-8f6c-a86737760226
-- title:
--   §§2, 4, 6 — list assignment, prefix finishing time, optimum, and longest remaining task
-- statement:
--   For independent tasks of lengths $\mu_j$ on $n$ identical processors, a priority list $L$ contains every task once. An assignment $\sigma$ names the processor of each task. The **load before position $k$** on processor $p$ is the sum of the lengths assigned to $p$ among the first $k$ list positions. An assignment obeys Graham's **list rule** if every task is sent to a processor whose load before that task is least.
--
--   The **prefix finishing time** is the largest processor load from the first $k$ tasks. The **optimal finishing time** $\omega_0$ is the least makespan over all assignments of all tasks. The **longest remaining length** $\alpha^*$ is the maximum length outside the first $k$ positions.
--
--   These objects express both the algorithm and the lower bounds in Theorem 3. With no precedence constraints, processors work continuously from time zero while unstarted tasks remain, so a list run is determined by its least-loaded assignments. Every partition of the task lengths can be realized by an ordering, making the assignment minimum equal to the paper's minimum over lists.
--
--   **Formalization Note** Tasks and processors are zero-based finite types. Ties between least-loaded processors are free: the paper's smaller-index tie convention changes no finishing time. Finite maxima and minima return zero only in the degenerate empty-carrier branches; theorem statements require $n>0$, and those using $\alpha^*$ require $k<r$.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), pp. 416, 421, 426–428, §2 system, §4 ω₀, §6 Theorem 3 and partition form

import Mathlib
import Definitions.Def_WilliamsonShmoys_ParallelMakespan

namespace GrahamAnomaly.KLongest

/-- Load of processor `p` after the first `k` jobs in the priority list. -/
noncomputable def loadBefore {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) (k : ℕ) (p : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < k ∧ σ j = p), μ j

/-- Each successive job is assigned to a processor with minimum current load. -/
def IsListAssignment {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) : Prop :=
  ∀ j : Fin r, ∀ p : Fin n,
    loadBefore μ L σ (L.symm j) (σ j) ≤ loadBefore μ L σ (L.symm j) p

/-- The latest completion time among the first `k` jobs of the list. -/
noncomputable def prefixFinish {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) (k : ℕ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.sup' h (loadBefore μ L σ k)
  else 0

/-- Least makespan among all assignments of the jobs to the processors. -/
noncomputable def optFinish {r : ℕ} (μ : Fin r → ℝ) (n : ℕ) : ℝ :=
  if h : (Finset.univ : Finset (Fin r → Fin n)).Nonempty then
    Finset.univ.inf' h (WilliamsonShmoys.makespan μ)
  else 0

/-- Length of the longest job after the first `k` positions; zero if none remain. -/
noncomputable def alphaStar {r : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r)
    (k : ℕ) : ℝ :=
  if h : (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).Nonempty then
    (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).sup' h μ
  else 0

end GrahamAnomaly.KLongest


