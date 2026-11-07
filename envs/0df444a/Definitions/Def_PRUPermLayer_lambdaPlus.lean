-- Prove2me | Definitions.Def_PRUPermLayer_lambdaPlus
-- name    : PRUPermLayer_lambdaPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:27.418685+00:00
-- url     : https://prove2.me/theorems/8cdd867b-8f4e-45db-a01a-0b36067944cc
-- title:
--   Plus parameter $\lambda_+(\mu) = \|H_\mu\|$
-- statement:
--   The **plus parameter** of a distribution $\mu$ on $U(2)$ is the operator norm $\lambda_+(\mu) = \|H_\mu\|$ of its plus operator. For the uniform Clifford distribution it equals $1/2$ (Eq. (3)).
--
--   **Formalization Note** Spectral norm. Sanity: for the point mass at the identity it is $1$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_PRUPermLayer_plusOp
open MeasureTheory

namespace PRUPermLayer

/-- The plus parameter `λ₊(µ) = ‖H_µ‖`, an operator norm (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)).

**Formalization Note** `‖·‖` is `QAlgorithms.specNorm`. Sanity: `lambdaPlus (dirac 1) = 1`. -/
noncomputable def lambdaPlus (μ : Measure (Matrix.unitaryGroup Bool ℂ)) : ℝ :=
  QAlgorithms.specNorm (plusOp μ)

end PRUPermLayer


