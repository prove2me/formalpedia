-- Prove2me | Definitions.Def_SymNormLoad_loadVec
-- name    : SymNormLoad_loadVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:43.613328+00:00
-- url     : https://prove2.me/theorems/42305254-b4ad-429f-81dd-4c385a9aed12
-- title:
--   Load vector $L_i=\sum_{j:\,i_j=i}p_{ji}$ of an assignment
-- statement:
--   In the unrelated-machine model, job $j$ has a processing-time vector $p_j=(p_{j1},\dots,p_{jM})\in\mathbb R^M_{\ge0}$. If job $j$ is assigned to machine $i_j$, the **load vector** $L=(L_1,\dots,L_M)$ is
--   $$
--   L_i=\sum_{j:\ i_j=i}p_{ji}.
--   $$
--
--   This is the vector to which the objective $\Psi$ is applied, both for the online algorithm and for any offline assignment.
--
--   **Formalization Note** Jobs are `Fin N` and machines `Fin M`, both 0-based; the assignment is a map $\sigma$ from jobs to machines. Nonnegativity of $p$ is a hypothesis of the theorems.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 1.1, pp.2–3

import Mathlib

namespace SymNormLoad

/-- **Load vector of an integral assignment.** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), §1.1, pp.2–3: in the unrelated-machine
model job `j` reveals a processing-time vector `p_j = (p_{j1}, …, p_{jM})`; if job `j` is
assigned to machine `i_j`, the load vector is `L_i = ∑_{j : i_j = i} p_{ji}`.

**Formalization Note** Jobs are `Fin N` and machines `Fin M`, both 0-based; `p j i` is the
processing time of job `j` on machine `i`, and `σ j` the machine of job `j`. Nonnegativity of
`p` is a hypothesis of each statement, not part of this definition. -/
def loadVec {N M : ℕ} (p : Fin N → Fin M → ℝ) (σ : Fin N → Fin M) : Fin M → ℝ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j => σ j = i), p j i

end SymNormLoad


