-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Supplement_Spectral
-- name    : SuperRamanujan227_Main_Supplement_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:41:39.993726+00:00
-- url     : https://prove2.me/theorems/499ac91f-349d-42bf-967f-a1116dd73caa
-- title:
--   Bipartitions and two-sided nontrivial adjacency spectrum
-- statement:
--   For a natural adjacency matrix $A$ of order $n$, a bipartition is a Boolean coloring $c$ such that $A_{uv}=0$ whenever $c(u)=c(v)$. Edge multiplicities are preserved and a bipartition excludes loops. Order the real adjacency eigenvalues with multiplicity as $\lambda_1\ge\cdots\ge\lambda_n$. Define
--
--   $$
--   \lambda(A)=\max\bigl(\{0\}\cup\{|\lambda_k|:2\le k\le n,\ \text{and }k<n\text{ if }A\text{ is bipartite}\}\bigr).
--   $$
--
--   Thus exactly one occurrence of $d$ and, in the bipartite case, one occurrence of $-d$ are removed in a $d$-regular graph. Additional occurrences remain and detect disconnectedness. An empty residual spectrum has value zero. The graph version uses the immutable base adjacency model and root ordering. This definition supplies the two-sided parameter required by the constructive and arithmetic companion theorems.
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), pp. 2, 6–7, spectral expansion convention

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Multigraph

namespace SuperRamanujan227.Main.Supplement

/-- A Boolean bipartition of the support of an adjacency matrix. Parallel edges are retained. -/
def MatrixBipartite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ c : Fin n → Bool, ∀ u v, c u = c v → A u v = 0

/-- Exactly one occurrence of the top eigenvalue is removed; in the bipartite case exactly
one bottom occurrence is also removed. Extra copies of ±d in disconnected graphs remain.
The maximum of an empty residual spectrum is zero. -/
noncomputable def nontrivialRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : ℝ := by
  classical
  exact (((List.range (n + 1)).filter fun k =>
    2 ≤ k ∧ k ≤ n ∧ (¬ MatrixBipartite A ∨ k < n)).map
    (fun k => |matrixEig (A.map (fun a => (a : ℝ))) k|)).foldl max 0

/-- The two-sided, unnormalized nontrivial adjacency spectral parameter. -/
noncomputable def spectralRadius {n : ℕ} (G : Multigraph n) : ℝ :=
  nontrivialRadius G.adj

end SuperRamanujan227.Main.Supplement


