-- Prove2me | Definitions.Def_EulerSparsify_nnz
-- name    : EulerSparsify_nnz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:22.900574+00:00
-- url     : https://prove2.me/theorems/968f7aaf-3bdd-4fb1-8574-90330ea799ce
-- title:
--   Number of nonzero entries $\mathrm{nnz}(x)$
-- statement:
--   For $x\in\mathbb R^E$, $\mathrm{nnz}(x)=|\{e\in E: x_e\neq 0\}|$ is the number of nonzero entries, and $\mathrm{supp}(x)$ is the set of these indices. For new edge weights $w'$, $\mathrm{nnz}(w')$ is the number of edges of the reweighted graph $(V,\mathrm{supp}(w'),w')$, i.e. $|E(\vec H)|$ in Theorem 1.2.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Linear algebra, p.8 (PDF p.10)

import Mathlib

namespace EulerSparsify

/-- **Number of nonzero entries** `nnz(x)` (§3, "Linear algebra", p.8, PDF p.10).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, p.8: "The number of nonzero entries of a matrix M (resp. vector v) is denoted nnz(M)
(resp. nnz(v)), and the subset of indices with nonzero entries is supp(M) (resp. supp(v))."

For a reweighting `w'` of a graph, `nnz w'` is the number of edges of the reweighted graph
`(V, supp(w'), w')`, i.e. `|E(⃗H)|` in Theorem 1.2. -/
noncomputable def nnz {E : Type} [Fintype E] (x : E → ℝ) : ℕ :=
  (Finset.univ.filter fun e => x e ≠ 0).card

end EulerSparsify


