-- Prove2me | Definitions.Def_PRUPermLayer_deltaEq
-- name    : PRUPermLayer_deltaEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:11.367366+00:00
-- url     : https://prove2.me/theorems/9e8ca212-3bbe-4196-a95b-5886926fa21c
-- title:
--   Collision parameter $\delta_{\mathrm{eq}}(\mu) = \|A_\mu\|$
-- statement:
--   The **collision parameter** of a distribution $\mu$ on $U(2)$ is the operator norm $\delta_{\mathrm{eq}}(\mu) = \|A_\mu\|$ of its collision operator. For the uniform Clifford distribution it equals $2/3$ (Eq. (3)).
--
--   **Formalization Note** Spectral norm. Sanity: for the point mass at the identity it is $1$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_PRUPermLayer_collisionOp
open MeasureTheory

namespace PRUPermLayer

/-- The collision parameter `δ_eq(µ) = ‖A_µ‖`, an operator norm (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.6, p.11
(PDF p.13)).

**Formalization Note** `‖·‖` is `QAlgorithms.specNorm`. Sanity: `deltaEq (dirac 1) = 1`. -/
noncomputable def deltaEq (μ : Measure (Matrix.unitaryGroup Bool ℂ)) : ℝ :=
  QAlgorithms.specNorm (collisionOp μ)

end PRUPermLayer


