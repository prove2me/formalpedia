-- Prove2me | Definitions.Def_SConvexGS_SExc
-- name    : SConvexGS_SExc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:13.763946+00:00
-- url     : https://prove2.me/theorems/4662daf8-3b53-4d02-a599-2876d1816e5b
-- title:
--   Exchange property (S-EXC)
-- statement:
--   A function $g:\mathbb R^n\to(-\infty,\infty]$ satisfies (S-EXC) if for any $x,y\in\operatorname{dom}(g)$ and $i\in\operatorname{supp}^+(x-y)$, there exist $j\in\operatorname{supp}^-(x-y)\cup\{0\}$ and $\alpha_0,\beta>0$ such that for any $\alpha\in[0,\alpha_0]$,
--
--   $$g(x)+g(y)\ge g\bigl(x-\alpha(\mathbf e_i-\beta\mathbf e_j)\bigr)+g\bigl(y+\alpha(\mathbf e_i-\beta\mathbf e_j)\bigr).$$
--
--   Here $\operatorname{supp}^+(x-y)=\{i\mid x_i>y_i\}$ and $\operatorname{supp}^-(x-y)=\{i\mid x_i<y_i\}$. The property says that moving $x$ and $y$ towards each other along $\mathbf e_i-\beta\mathbf e_j$ does not raise $g(x)+g(y)$. With $\beta=1$ it becomes the exchange property of M$^\natural$-convexity (Remark 1).
--
--   **Formalization Note** The indices $j$ and the constants $\alpha_0,\beta$ are chosen after $x,y,i$ and before $\alpha$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Definition 1, (S-EXC), p.10

import Mathlib
import Definitions.Def_SConvexGS_dom
import Definitions.Def_SConvexGS_basisOrZero

namespace SConvexGS

/-- The exchange property (S-EXC) (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632
(PDF of 2021-10-29), Definition 1, p.10): for any `x, y ∈ dom(g)` and `i ∈ supp⁺(x − y)`, there
exist `j ∈ supp⁻(x − y) ∪ {0}` and `α₀, β > 0` such that for any `α ∈ [0, α₀]`,
`g(x) + g(y) ≥ g(x − α(eᵢ − βeⱼ)) + g(y + α(eᵢ − βeⱼ))`.

Formalization Note: `i ∈ supp⁺(x − y)` is `y i < x i`, and `j ∈ supp⁻(x − y) ∪ {0}` is `j = none`
or `j = some j'` with `x j' < y j'` (`basisOrZero`). `α₀` and `β` are chosen after `x, y, i` and
before `α`, and `α` ranges over the closed interval. The property is used for `g` with no value
`⊥`, so that both sides lie in `(−∞, ∞]`. -/
def SExc {n : ℕ} (g : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x ∈ dom g, ∀ y ∈ dom g, ∀ i : Fin n, y i < x i →
    ∃ j : Option (Fin n), (j = none ∨ ∃ j' : Fin n, j = some j' ∧ x j' < y j') ∧
      ∃ α₀ : ℝ, 0 < α₀ ∧ ∃ β : ℝ, 0 < β ∧ ∀ α ∈ Set.Icc (0 : ℝ) α₀,
        g (x - α • (basisOrZero (some i) - β • basisOrZero j)) +
            g (y + α • (basisOrZero (some i) - β • basisOrZero j)) ≤ g x + g y

end SConvexGS


