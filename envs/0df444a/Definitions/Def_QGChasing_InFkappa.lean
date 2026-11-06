-- Prove2me | Definitions.Def_QGChasing_InFkappa
-- name    : QGChasing_InFkappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:40.453038+00:00
-- url     : https://prove2.me/theorems/bb6bff31-0087-488b-b306-228f64efba70
-- title:
--   One round of the class $\mathcal F_\kappa$ (Assumptions 2, 3, 5)
-- statement:
--   Fix $\kappa\in\mathbb R$. A hitting cost $f:\mathbb R^d\to\mathbb R$ **belongs to $\mathcal F_\kappa$** if
--
--   1. $f\ge0$ and $f$ is convex (Assumption 2);
--   2. there are $v\in\mathbb R^d$ and $\lambda>0$ such that $f$ has $\lambda$-quadratic growth at $v$ on all of $\mathbb R^d$ (Assumption 3, Eq. (1));
--   3. there is $L>0$ with $L\le\kappa\lambda$ such that $f$ is $L$-smooth: differentiable on $\mathbb R^d$ with $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$ (Assumption 5).
--
--   A sequence of hitting costs lies in $\mathcal F_\kappa$ when each $f_t$ does; the parameters $\lambda_t$, $L_t$ and the minimizer $v_t$ may change from round to round, while $\kappa$ is fixed. This is the cost class of Theorem 1.1.
--
--   **Formalization Note** The parameters are existential inside the predicate, so they are per round. The global-minimum clause of Assumption 3 is implied by quadratic growth with $\lambda>0$ and is not repeated. Smoothness is the published definition `HomotopyProxVM.IsSmoothParam`, which also records $0\le L$ (implied by $L>0$). Assumption 1 is about the decision set and is a hypothesis of the theorems.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), p.2 (definition of F_κ) with Assumptions 2, 3 and 5, p.4

import Mathlib
import Definitions.Def_QGChasing_HasQuadGrowth
import Definitions.Def_HomotopyProxVM_IsSmoothParam

namespace QGChasing

/-- One round of the class `F_κ` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.2, with Assumptions 2, 3 and 5, p.4): the hitting
cost `f : ℝᵈ → ℝ` is nonnegative and convex (Assumption 2), has `λ`-quadratic growth on `ℝᵈ` at
some point `v` for some `λ > 0` (Assumption 3, Eq. (1)), and is `L`-smooth (differentiable with
`L`-Lipschitz gradient) for some `L > 0` with `L ≤ κλ` (Assumption 5).

**Formalization Note** `λ` (named `lam`), `L` and `v` are existential inside one round, so a
sequence `f₁, f₂, …` with every `f_t` in `F_κ` has per-round parameters `λ_t`, `L_t`, `v_t`
("The parameters may vary across rounds", p.2); `κ` is fixed. The global minimum of Assumption 3 is
not a separate clause: quadratic growth at `v` with `λ > 0` makes `v` the global minimizer.
Smoothness is the published `HomotopyProxVM.IsSmoothParam` (differentiable on `ℝᵈ`,
`‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖`, and `0 ≤ L`, implied by `0 < L`). Assumption 1 concerns the decision
set and appears in the theorems. -/
def InFkappa {d : ℕ} (κ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ConvexOn ℝ Set.univ f ∧
    ∃ v : EuclideanSpace ℝ (Fin d), ∃ lam L : ℝ, 0 < lam ∧ 0 < L ∧ L ≤ κ * lam ∧
      HasQuadGrowth lam f v ∧ HomotopyProxVM.IsSmoothParam f L

end QGChasing


