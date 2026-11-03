-- Prove2me | Definitions.Def_SparseBatchBandit_supp
-- name    : SparseBatchBandit_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:56.945226+00:00
-- url     : https://prove2.me/theorems/62edd97f-61fa-4e7b-9411-b5313cc817ca
-- title:
--   Support of a vector
-- statement:
--   The **support** of a vector $v\in\mathbb R^d$ is the set of its nonzero coordinates,
--
--   $$
--   \mathrm{supp}(v)=\{j\in[d]: v_j\neq 0\}.
--   $$
--
--   The set $S_0=\mathrm{supp}(\theta^\star)$ is the index set on which the cone condition of the Lasso analysis is stated.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, proof of Lemma 6, p.28

import Mathlib

namespace SparseBatchBandit

/-- The support `supp(v) = {j : v_j ≠ 0}` of a vector `v ∈ ℝ^d`, written `S₀ = supp(θ⋆)` in
Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, proof of Lemma 6, p.28 (PDF 28). -/
noncomputable def supp {d : ℕ} (v : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter (fun j => v j ≠ 0)

end SparseBatchBandit


