-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
-- name    : HighDimStat_RandomMatrices_adjacencyMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:20:18.509974+00:00
-- url     : https://prove2.me/theorems/990912d6-72c0-42f4-ba54-76441803e239
-- title:
--   The adjacency matrix of a covariance matrix's sparsity graph
-- statement:
--   The **adjacency matrix** $A$ of the sparsity graph of $\Sigma$:
--
--   $$
--   A_{j\ell} \;:=\; \mathbb 1[\Sigma_{j\ell}\neq 0].
--   $$
--
--   Its operator norm $|\!|\!|A|\!|\!|_2$ is the measure of sparsity Theorem 6.23's error bound
--   scales with.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 181 (PDF p. 201)

import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **adjacency matrix** `A` of the sparsity graph of `Σ`, Wainwright, *High-Dimensional
Statistics* (2019), p. 181: `A_{jℓ} := I[Σ_{jℓ} ≠ 0]`. -/
noncomputable def adjacencyMatrix {d : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j l => if Sig j l ≠ 0 then 1 else 0

end HighDimStat.RandomMatrices


