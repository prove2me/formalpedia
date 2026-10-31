-- Prove2me | Definitions.Def_DynChoiceJEO_fval
-- name    : DynChoiceJEO_fval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:43.747368+00:00
-- url     : https://prove2.me/theorems/9d0cd8fd-adbb-4975-b9f9-0b6ec238bc69
-- title:
--   Primal objective $f(x;p)=\max_{y\in Y}\Psi(x,y;p)$
-- statement:
--   For a saddle function $\Psi:\mathbb R^N\times\mathbb R^k\times\mathcal P\to\mathbb R$ (data space $\mathcal P$) and a set $Y\subseteq\mathbb R^k$, the **primal objective** is
--
--   $$f(x;p):=\max_{y\in Y}\Psi(x,y;p).$$
--
--   The primal problem is $\mathcal P(p)=\min_{x\in X}f(x;p)$. In the choice-model application $f(x;p)$ is the distance $D(x,p)$ between a choice-probability vector $x$ and the data $p$.
--
--   **Formalization Note** The maximum is the real supremum of $\{\Psi(x,y;p):y\in Y\}$. Under the standing assumptions (Y nonempty compact convex, $\Psi$ concave in $y$) this set is nonempty and bounded above, so the value is the paper's.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (7a), p.9

import Mathlib

namespace DynChoiceJEO

/-- **Primal objective `f(x;p) := max_{y∈Y} Ψ(x,y;p)`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (7a), p.9: "P(p) := min_{x∈X} f(x;p), f(x;p) := max_{y∈Y} Ψ(x,y;p)".

For a saddle function `Ψ : ℝᴺ → ℝᵏ → P → ℝ` (data space `P`), a dual set `Y ⊆ ℝᵏ`, a primal
point `x` and data `q`, `fval Ψ Y x q` is the supremum of `Ψ(x,·;q)` over `Y`.

**Formalization Note** The paper's `max` is the real supremum `sSup` of the image. Lean's
`sSup` is `0` on an empty or unbounded-above set; under the paper's standing assumptions (Y
nonempty compact convex, Ψ concave in y) the image is nonempty and bounded above, so `fval` is
the paper's value (attained or not). -/
noncomputable def fval {N k : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (Y : Set (Fin k → ℝ)) (x : Fin N → ℝ) (q : P) : ℝ :=
  sSup ((fun y => Ψ x y q) '' Y)

end DynChoiceJEO


