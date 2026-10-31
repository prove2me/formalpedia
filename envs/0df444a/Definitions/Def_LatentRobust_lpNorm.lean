-- Prove2me | Definitions.Def_LatentRobust_lpNorm
-- name    : LatentRobust_lpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:32.728128+00:00
-- url     : https://prove2.me/theorems/157516c9-5f40-4bbb-9255-5d3b4f2b63c1
-- title:
--   The $\ell_p$ norm $\|x\|_{\ell_p}=(\sum_i|x_i|^p)^{1/p}$
-- statement:
--   For a vector $x\in\mathbb R^d$ and a real exponent $p\ge 1$, the **$\ell_p$ norm** is
--   $$
--   \|x\|_{\ell_p}=\Big(\sum_{i=1}^d |x_i|^p\Big)^{1/p}.
--   $$
--   The case $p=2$ is the Euclidean norm, and the closed $\ell_2$ ball $B_\varepsilon(x)=\{x':\|x'-x\|_{\ell_2}\le\varepsilon\}$ is the ball of the paper's notation.
--
--   The norm measures the size of an adversarial perturbation: an $\ell_p$ adversary of power $\varepsilon_p$ may move a test point anywhere in the $\ell_p$ ball of radius $\varepsilon_p$.
--
--   **Formalization Note** Vectors are functions $\{1,\dots,d\}\to\mathbb R$ and the powers are real powers. The page prints $(\sum x_i^p)^{1/p}$; the absolute values are the standard reading.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §1.1 Notation, p.4

import Mathlib

namespace LatentRobust

/-- The `ℓp` norm of a vector of `ℝ^d` (Javanmard, Mehrabi, arXiv:2110.11950v2, §1.1 Notation,
p.4): `‖x‖_{ℓp} = (∑_{i=1}^d |x_i|^p)^{1/p}`, for a real exponent `p ≥ 1`.

**Formalization Note** The page prints `(∑ x_i^p)^{1/p}`; the absolute values are the standard
reading (without them the expression is not a norm for odd or non-integer `p`). Vectors are
functions `Fin d → ℝ`, powers are real powers (`Real.rpow`). The definition is used only for
`p ≥ 2` in this mission; `lpNorm 2` is the Euclidean norm, so the `ℓ2` ball `B_ε(x)` of p.4 is
`{x' | lpNorm 2 (x' - x) ≤ ε}` (closed). -/
noncomputable def lpNorm {d : ℕ} (p : ℝ) (v : Fin d → ℝ) : ℝ :=
  (∑ i, |v i| ^ p) ^ (1 / p)

end LatentRobust


