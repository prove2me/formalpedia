-- Prove2me | Definitions.Def_DualTwoStageRO_conj
-- name    : DualTwoStageRO_conj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:58.018015+00:00
-- url     : https://prove2.me/theorems/94f13586-315e-409b-8b33-0aa4abb90f88
-- title:
--   Convex conjugate $g^*$ of a real-valued function on $\mathbb R^n$
-- statement:
--   For a real-valued function $g:\mathbb R^n\to\mathbb R$, the **convex conjugate** is
--
--   $$g^*(s)=\sup_{y\in\mathbb R^n}\bigl\{s^\top y-g(y)\bigr\}\in(-\infty,+\infty],\qquad s\in\mathbb R^n .$$
--
--   Since $g$ is finite everywhere, $\operatorname{dom}g=\mathbb R^n$, so this is the page's $\sup_{\nu\in\operatorname{dom}(g)}$. The value is never $-\infty$ and may be $+\infty$.
--
--   The conjugates of the recourse functions $g_i$ define the uncertainty set $\mathcal V$ of the dualized model (6).
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with the pairing $s^\top y=\sum_j s_jy_j$. The supremum is taken in `EReal`, so it is the true supremum, $+\infty$ exactly when $s^\top y-g(y)$ is unbounded above. The platform's `ConvexOptimization.fenchelConjugate` is the same object on `EuclideanSpace`; it is not reused because every vector of this mission is `Fin n → ℝ` and is multiplied by matrices.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), §1.4, p.1795 (definition of g*)

import Mathlib

namespace DualTwoStageRO

/-- **Convex conjugate** of a real-valued function on `ℝⁿ`.
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, §1.4, p.1795: "The function g∗ is the convex
conjugate of the function g : R^{nν} → R and is defined by g∗(z) = sup_{ν∈dom(g)} {ν⊤z − g(ν)}".

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ` with the pairing `s ⬝ᵥ y = ∑ j, s j * y j`. Since `h` is
real-valued, `dom h = ℝⁿ` and the supremum runs over all `y`. The value is taken in `EReal`, so it is
the true supremum; it is `⊤` exactly when `s ⬝ᵥ y − h y` is unbounded above, and it is never `⊥`. -/
noncomputable def conj {n : ℕ} (h : (Fin n → ℝ) → ℝ) (s : Fin n → ℝ) : EReal :=
  ⨆ y : Fin n → ℝ, ((s ⬝ᵥ y - h y : ℝ) : EReal)

end DualTwoStageRO


