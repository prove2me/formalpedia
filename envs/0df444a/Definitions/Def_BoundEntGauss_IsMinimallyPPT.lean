-- Prove2me | Definitions.Def_BoundEntGauss_IsMinimallyPPT
-- name    : BoundEntGauss_IsMinimallyPPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:42.54965+00:00
-- url     : https://prove2.me/theorems/9f7633c4-910f-4974-9e48-69fc91b6c5e4
-- title:
--   Minimally ppt covariance (Definition 1)
-- statement:
--   A real symmetric matrix $\gamma$ is **minimally ppt** if it is a ppt-covariance and every ppt-covariance $\gamma'$ with $\gamma\ge\gamma'$ (that is, $\gamma-\gamma'$ positive semidefinite) is equal to $\gamma$.
--
--   Minimally ppt covariances are the extreme ppt-covariances from below. The paper reduces the question "does ppt imply separability for Gaussian states?" to whether minimally ppt covariances are block diagonal.
--
--   **Formalization Note** $\gamma'$ ranges over all bipartite covariance matrices with the same mode numbers; equality is of the assembled matrices.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Definition 1, p. 3

import Mathlib
import Definitions.Def_BoundEntGauss_IsPPTCovariance

open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks covarianceBlockMatrix)

namespace BoundEntGauss

/-- **Minimally ppt covariance.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Definition 1, p. 3.

A real symmetric `γ` is *minimally ppt* if it is a ppt-covariance and every ppt-covariance `γ'`
with `γ ≥ γ'` (i.e. `γ − γ'` positive semidefinite) equals `γ`.

**Formalization Note.** `γ'` ranges over all bipartite matrices of the same mode numbers
`n × m`; the comparison is between the assembled matrices, not the block records. -/
def IsMinimallyPPT {n m : ℕ} (g : CovarianceBlocks n m) : Prop :=
  IsPPTCovariance g ∧
    ∀ g' : CovarianceBlocks n m, IsPPTCovariance g' →
      (covarianceBlockMatrix g - covarianceBlockMatrix g').PosSemidef →
      covarianceBlockMatrix g' = covarianceBlockMatrix g

end BoundEntGauss


