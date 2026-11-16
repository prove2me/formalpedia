-- Prove2me | Definitions.Def_QMultiMean_Supplement_lpNorm
-- name    : QMultiMean_Supplement_lpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:13:05.284299+00:00
-- url     : https://prove2.me/theorems/efe47369-9a1b-4c26-9597-4e38e57ada32
-- title:
--   The $\ell_p$ norm $\|x\|_p$ on $\mathbb R^d$
-- statement:
--   For $p\in[1,\infty)$ and $x\in\mathbb R^d$, the **$\ell_p$ norm** is
--   $$\|x\|_p=\Big(\sum_{i=1}^d|x_i|^p\Big)^{1/p}.$$
--   The $\ell_1$ norm $\|x\|_1=\sum_i|x_i|$ is the case $p=1$; the $\ell_\infty$ norm $\max_i|x_i|$ is the published `QMultiMean.supNorm`.
--
--   These norms measure the error of the phase-oracle estimators of Theorem 4.5 and of the lower bounds of Theorems 4.7, 4.9 and 4.10.
--
--   **Formalization Note** The ambient space `Vec d` carries the Euclidean norm, so $\|\cdot\|_p$ is a separate function, computed with real powers; it is used only for $p\ge1$.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.6, Definition 2.1

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- The `ℓ_p` norm `‖x‖_p = (Σ_{i ∈ [d]} |x_i|^p)^{1/p}` of a vector `x ∈ ℝ^d`, for `p ∈ [1, ∞)`
(Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum Algorithms for Multivariate Mean Estimation*,
arXiv:2111.09787v2, Definition 2.1, p.6). The `ℓ₁` norm is the case `p = 1`; the `ℓ∞` norm is the
published `QMultiMean.supNorm`.

**Formalization Note.** `Vec d` carries the `ℓ₂` norm, so the `ℓ_p` norm is a separate function,
computed with the real power `Real.rpow` (`|x_i|^p` is a power of a nonnegative real). It is used only
for `p ≥ 1`. -/
noncomputable def lpNorm {d : ℕ} (p : ℝ) (x : Vec d) : ℝ :=
  (∑ i : Fin d, |x i| ^ p) ^ (1 / p)

end QMultiMean.Supplement


