-- Prove2me | Definitions.Def_SymNormLoad_greedyLoad
-- name    : SymNormLoad_greedyLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:29.906558+00:00
-- url     : https://prove2.me/theorems/8a8b1bfc-e1f4-4d1d-a6f3-3043589cc393
-- title:
--   Final load vector of the potential greedy (Algorithm 2.4)
-- statement:
--   **Algorithm 2.4 (potential greedy).** Initialize $L=0$. When job $j$ arrives with processing times $p_j$, choose
--   $$
--   i_j\in\arg\min_{i\in[M]}\bigl\{g(L_i+p_{ji})-g(L_i)\bigr\},\tag{2.4}
--   $$
--   breaking ties by the smallest index, assign the whole job to $i_j$ and increase $L_{i_j}$ by $p_{j,i_j}$. The **final load vector** is $L$ after all $N$ jobs.
--
--   The algorithm uses only the current loads and the current job, so it is online.
--
--   **Formalization Note** Machines are 0-based and "smallest index" is the least element of `Fin M`. Auxiliary definitions in the same module: the cost $g(L_i+q_i)-g(L_i)$, the argmin set, one step, and the loads after each prefix. The algorithm runs on $p$ as given; the paper's normalization is a hypothesis of the theorems that need it.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Algorithm 2.4 and Eq. (2.4), p.10

import Mathlib
import Definitions.Def_SymNormLoad_pen

namespace SymNormLoad

/-- The increase `g(L_i + q_i) − g(L_i)` of machine `i`'s penalty if the current job, with
processing-time vector `q`, is put on machine `i` while the loads are `L`. -/
noncomputable def greedyCost {M : ℕ} (h : ℝ → ℝ) (L q : Fin M → ℝ) (i : Fin M) : ℝ :=
  pen h (L i + q i) - pen h (L i)

/-- The set `arg min_{i ∈ [M]} {g(L_i + q_i) − g(L_i)}` of (2.4). -/
noncomputable def greedyArgmin {M : ℕ} (h : ℝ → ℝ) (L q : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => ∀ i', greedyCost h L q i ≤ greedyCost h L q i')

/-- One step of Algorithm 2.4: put the job on the smallest-index minimizer of (2.4) and add its
processing time there. (When `M = 0` there is no machine and the loads are unchanged.) -/
noncomputable def greedyStep {M : ℕ} (h : ℝ → ℝ) (L q : Fin M → ℝ) : Fin M → ℝ :=
  if hS : (greedyArgmin h L q).Nonempty then
    Function.update L ((greedyArgmin h L q).min' hS) (L ((greedyArgmin h L q).min' hS) +
      q ((greedyArgmin h L q).min' hS))
  else L

/-- The loads `L^{(n)}` of Algorithm 2.4 after the first `n` jobs (`L^{(0)} = 0`). -/
noncomputable def greedyLoadPrefix {N M : ℕ} (h : ℝ → ℝ) (p : Fin N → Fin M → ℝ) :
    ℕ → Fin M → ℝ
  | 0 => 0
  | n + 1 =>
    if hn : n < N then greedyStep h (greedyLoadPrefix h p n) (p ⟨n, hn⟩)
    else greedyLoadPrefix h p n

/-- **Final load vector of Algorithm 2.4 (potential greedy).** Chen–Im–Sirri, *Online Load
Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), Algorithm 2.4 and (2.4),
p.10: initialize `L = 0`; when job `j` arrives choose
`i_j ∈ arg min_{i ∈ [M]} {g(L_i + p_{ji}) − g(L_i)}`, breaking ties by the smallest index, assign
the job to `i_j` and increase `L_{i_j}` by `p_{j,i_j}`. `greedyLoad h p` is the load vector after
all `N` jobs.

**Formalization Note** `g = exp ∘ h` is `pen h`. Jobs and machines are 0-based; "smallest index"
is the least element of `Fin M`. The algorithm is run on `p` as given (the "normalized instance"
is `p` itself; normalization is a hypothesis of the theorems that need it). -/
noncomputable def greedyLoad {N M : ℕ} (h : ℝ → ℝ) (p : Fin N → Fin M → ℝ) : Fin M → ℝ :=
  greedyLoadPrefix h p N

end SymNormLoad


