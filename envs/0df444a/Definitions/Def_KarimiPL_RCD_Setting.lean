-- Prove2me | Definitions.Def_KarimiPL_RCD_Setting
-- name    : KarimiPL_RCD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:12.272096+00:00
-- url     : https://prove2.me/theorems/69e9cc1f-eb3f-4a08-bc69-2376529d9502
-- title:
--   §3.1, p. 5 — coordinate smoothness, update (6), and uniform-draw expectation
-- statement:
--   Let $d$ be a nonnegative integer, let $f:\mathbb R^d\to\mathbb R$, and let $e_i$ be the $i$th coordinate vector. The **coordinate-wise upper bound** with constant $L$ is the condition
--
--   $$
--   f(x+\alpha e_i)\le f(x)+\alpha\nabla_i f(x)+\frac L2\alpha^2
--   \qquad(x\in\mathbb R^d,\ i\in\{1,\ldots,d\},\ \alpha\in\mathbb R).
--   $$
--
--   The coordinate-descent step and the run from $x_0$ are
--
--   $$
--   T_i(x)=x-\frac{\nabla_i f(x)}L e_i,\qquad
--   x_{t+1}=T_{i_t}(x_t).
--   $$
--
--   For a word $(i_0,\ldots,i_{k-1})$ of coordinate choices, $x_k$ is defined by these updates. Its **expected gap** relative to a value $f^*$ is
--
--   $$
--   \mathbb E[f(x_k)-f^*]=\frac1{d^k}\sum_{(i_0,\ldots,i_{k-1})\in\{1,\ldots,d\}^k}(f(x_k)-f^*).
--   $$
--
--   This gives each word the probability it has under independent uniform draws, including the empty word at $k=0$. These objects are the shared setting for Theorem 3 and its proof steps.
--
--   **Formalization Note** Coordinates are indexed by `Fin d`, starting at zero. The definitions are total for all $d$ and $L$; the theorems assume $d\ge1$ and $L>0$ wherever division or sampling requires them.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, §3.1, (5)–(6) and Theorem 3, p. 5

import Mathlib
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.RCD

/-- The coordinate-wise quadratic upper bound (5), with the same constant in every coordinate. -/
noncomputable def CoordLipschitz {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) : Prop :=
  ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (α : ℝ),
    f (x + α • EuclideanSpace.single i 1) ≤
      f x + α * gradient f x i + L / 2 * α ^ 2

/-- The coordinate update (6) when coordinate `i` is selected. -/
noncomputable def cdStep {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) (x : KarimiPL.Rel.E d) (i : Fin d) : KarimiPL.Rel.E d :=
  x - (1 / L * gradient f x i) • EuclideanSpace.single i 1

/-- The iterate after `k` coordinate choices, indexed by the complete choice word. -/
noncomputable def cdRun {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) (x0 : KarimiPL.Rel.E d) :
    (k : ℕ) → (Fin k → Fin d) → KarimiPL.Rel.E d
  | 0, _ => x0
  | k + 1, is => cdStep f L (cdRun f L x0 k (Fin.init is)) (is (Fin.last k))

/-- Expected suboptimality after `k` independent uniform coordinate choices. -/
noncomputable def expectedGap {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) (x0 : KarimiPL.Rel.E d)
    (fstar : ℝ) (k : ℕ) : ℝ :=
  (1 / (d : ℝ) ^ k) *
    ∑ is : Fin k → Fin d, (f (cdRun f L x0 k is) - fstar)

end KarimiPL.RCD


