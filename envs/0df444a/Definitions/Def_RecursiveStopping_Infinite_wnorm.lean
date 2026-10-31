-- Prove2me | Definitions.Def_RecursiveStopping_Infinite_wnorm
-- name    : RecursiveStopping_Infinite_wnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:20.000654+00:00
-- url     : https://prove2.me/theorems/8be6e38d-4454-4656-a819-95d7a907be6d
-- title:
--   The weighted norm $\|f\|_{\mathcal A_d}$
-- statement:
--   For a real function $f$ on $\mathbb R^d$,
--
--   $$
--   \|f\|_{\mathcal A_d}^2:=\sup_{x\in\mathbb R^d}\frac{|f(x)|^2}{1+|x|_d^2},
--   \qquad\text{i.e.}\qquad
--   \|f\|_{\mathcal A_d}=\sup_{x\in\mathbb R^d}\frac{|f(x)|}{(1+|x|_d^2)^{1/2}}\in[0,\infty],
--   $$
--
--   where $|\cdot|_d$ is the Euclidean norm. Finite norm means at most linear growth. This is the norm in which the operator $\Gamma$ is a contraction.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The norm is valued in $[0,\infty]$, so it is defined for every real function, including differences $f-g$.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (8), p.8

import Mathlib

open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- The weighted norm `∥f∥_{A_d}` of Colaneri & De Angelis, arXiv:1905.02650v4, (8), p.8:
$$\|f\|_{A_d}^2 := \sup_{x\in\mathbb R^d}\frac{|f(x)|^2}{1+|x|_d^2},$$
i.e. `∥f∥_{A_d} = sup_x |f(x)| / (1 + |x|_d²)^{1/2}`, with `|·|_d` the Euclidean norm.

**Formalization Note** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`, whose norm is `|·|_d`. The value is
in `[0, ∞]`, so the norm is defined for every real function (including differences `f − g`) and
is `∞` exactly when the ratio is unbounded. -/
noncomputable def wnorm {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal (|f x| / Real.sqrt (1 + ‖x‖ ^ 2))

end RecursiveStopping.Infinite


