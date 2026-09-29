-- Prove2me | Definitions.Def_HighDimProb_SparseRecovery_L2Norm
-- name    : HighDimProb_SparseRecovery_L2Norm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:01.257437+00:00
-- url     : https://prove2.me/theorems/bdc5b0df-d873-4516-8acc-e2dee92380f6
-- title:
--   The Euclidean ($\ell_2$) norm of a vector
-- statement:
--   The **Euclidean (`$\ell_2$`) norm** $\|v\|_2 := \sqrt{\sum_i v_i^2}$ of a vector $v$ indexed by
--   a finite type. Used both for the restricted isometry property (`SatisfiesRIP`) and for the
--   measurement model $y = Av$.
--
--   **Formalization Note** Stated on the plain function type `ι → ℝ` rather than `EuclideanSpace ℝ
--   ι`, so that the $\ell_1$ norm (`L1Norm`) and sparsity (`Sparsity`) needed by this chapter's
--   optimization programs can be stated on the same underlying type — `EuclideanSpace`'s own norm
--   instance is fixed to $\ell_2$ and cannot host $\ell_1$.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Section 10.3.1, standing notation

import Mathlib

namespace HighDimProb.SparseRecovery

/-- The **Euclidean (`ℓ2`) norm** `‖v‖₂` of a vector `v : ι → ℝ` indexed by a finite type `ι`,
`Real.sqrt (∑ i, v i ^ 2)`. Stated on the plain function type `ι → ℝ` rather than
`EuclideanSpace ℝ ι` so that `l1Norm` and `l0Sparsity` (Section 10.3.1's `‖·‖₁`, `‖·‖₀`) can be
stated on the same underlying type — `EuclideanSpace`'s own `Norm` instance is fixed to the `ℓ2`
norm and cannot host the `ℓ1` norm needed for the optimization program (10.12)/(10.22) this
chapter's theorems quantify over. -/
noncomputable def l2Norm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

end HighDimProb.SparseRecovery


