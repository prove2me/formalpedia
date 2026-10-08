-- Prove2me | Definitions.Def_BurnInBatch_TardyJobs_DP3Variable
-- name    : BurnInBatch_TardyJobs_DP3Variable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:12.800443+00:00
-- url     : https://prove2.me/theorems/bea17a6a-52ff-41c3-96e1-1fca6d57225f
-- title:
--   §4: DP3 transition with agreeable job-dependent processing times
-- statement:
--   For simultaneously available jobs with processing times $p_j$ and due dates $d_j$ in nondecreasing index order, the variable-time extension uses the same boundary conditions and skip transition as DP3. For $1\le k\le\min(B,i)$, the last-batch candidate is
--
--   $$
--   f_k(i,j)=\begin{cases}f(i-k,j-k)+p_j,&f(i-k,j-k)+p_j\le d_{j-k+1},\\+\infty,&\text{otherwise.}\end{cases}
--   $$
--
--   The table takes the minimum of these candidates and $f(i,j-1)$, and the largest finite count from $0$ through $n$ is named for the extension's correctness theorem.
--
--   **Formalization Note** Jobs are `Fin n`, so $p_j$ uses index $j-1$. The last job of a consecutive batch has the longest processing time under the stated index order. Empty transition ranges have value $+\infty$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 771, §4, extension of DP3 and displayed definition of f_k(i,j)

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- The §4 extension of DP3 to job-dependent processing times and no release times.
For a consecutive last on-time batch ending at job `j`, its duration is `p_j`. -/
def dp3Variable {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) (i j : ℕ) : WithTop ℕ :=
  if hi0 : i = 0 then 0
  else if hgt : i > j then ⊤
  else if hj : j ≤ n then
    have hi : i ≤ j := by omega
    have hjpos : 0 < j := by omega
    let skip := dp3Variable B p d i (j - 1)
    let take := (Finset.Icc 1 (min B i)).attach.inf (fun k =>
      let finish := dp3Variable B p d (i - k.val) (j - k.val) +
        ((p ⟨j - 1, by omega⟩ : ℕ) : WithTop ℕ)
      if finish ≤
        ((d ⟨j - k.val, by have hk := Finset.mem_Icc.mp k.property; omega⟩ : ℕ) : WithTop ℕ)
      then finish else ⊤)
    min take skip
  else ⊤
termination_by j
decreasing_by
  all_goals first | omega | (have hk := Finset.mem_Icc.mp k.property; omega)

def dp3VariableMaxOnTime {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) : ℕ :=
  Nat.findGreatest (fun i => dp3Variable B p d i n ≠ ⊤) n

end BurnInBatch.TardyJobs


