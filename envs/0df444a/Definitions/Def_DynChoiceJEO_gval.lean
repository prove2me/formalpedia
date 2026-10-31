-- Prove2me | Definitions.Def_DynChoiceJEO_gval
-- name    : DynChoiceJEO_gval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:42.213615+00:00
-- url     : https://prove2.me/theorems/0203b8c0-a2e7-4f10-82f8-c110a32ddcbe
-- title:
--   Dual objective $g(y;p)=\min_{x\in X}\Psi(x,y;p)$
-- statement:
--   For a saddle function $\Psi$ and a set $X\subseteq\mathbb R^N$, the **dual objective** is
--
--   $$g(y;p):=\min_{x\in X}\Psi(x,y;p).$$
--
--   The dual problem is $\mathcal D(p)=\max_{y\in Y}g(y;p)$.
--
--   **Formalization Note** The minimum is the real infimum of $\{\Psi(x,y;p):x\in X\}$, which is nonempty and bounded below under the standing assumptions (X nonempty compact convex, $\Psi$ convex in $x$).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (7b), p.9

import Mathlib

namespace DynChoiceJEO

/-- **Dual objective `g(y;p) := min_{x∈X} Ψ(x,y;p)`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (7b), p.9: "D(p) := max_{y∈Y} g(y;p), g(y;p) := min_{x∈X} Ψ(x,y;p)".

`gval Ψ X y q` is the infimum of `Ψ(·,y;q)` over the primal set `X ⊆ ℝᴺ`.

**Formalization Note** The paper's `min` is the real infimum `sInf` of the image. Lean's
`sInf` is `0` on an empty or unbounded-below set; under the standing assumptions (X nonempty
compact convex, Ψ convex in x) the image is nonempty and bounded below. -/
noncomputable def gval {N k : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (y : Fin k → ℝ) (q : P) : ℝ :=
  sInf ((fun x => Ψ x y q) '' X)

end DynChoiceJEO


