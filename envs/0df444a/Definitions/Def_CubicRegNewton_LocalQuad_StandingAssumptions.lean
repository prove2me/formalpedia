-- Prove2me | Definitions.Def_CubicRegNewton_LocalQuad_StandingAssumptions
-- name    : CubicRegNewton_LocalQuad_StandingAssumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:51.145629+00:00
-- url     : https://prove2.me/theorems/6610d56a-dd03-4d10-822c-45725756a6b0
-- title:
--   Standing assumptions of §2 and Assumption 1 (Lipschitz Hessian on $F$)
-- statement:
--   Let $F\subseteq\mathbb R^n$, $f:F\to\mathbb R$, a point $x_0$ and $L\in\mathbb R$. The **standing assumptions** of the paper hold when:
--
--   1. $F$ is closed and convex, and $x_0\in\operatorname{int}F$ (so $F$ has non-empty interior);
--   2. the level set $\mathcal L(f(x_0))=\{x\in F: f(x)\le f(x_0)\}$ lies in $\operatorname{int}F$;
--   3. $f$ is twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$ at every $x\in F$;
--   4. the Hessian is Lipschitz continuous on $F$ (Assumption 1, (2.1)): for some $L>0$,
--   $$
--   \|f''(x)-f''(y)\|\le L\|x-y\|\qquad\forall x,y\in F,
--   $$
--   where $\|\cdot\|$ is the spectral norm.
--
--   These are the assumptions under which every result of §§2–3 is proved; $x_0$ is the starting point of the iterative schemes.
--
--   **Formalization Note** The gradient `f'` and the Hessian `f''` are data, required to be the derivatives of `f` and `f'` within $F$ at each point of $F$; on a convex set with non-empty interior they are unique, and $f''(x)$ is symmetric (a consequence, not an assumption). Values of `f`, `f'`, `f''` outside $F$ are unconstrained. The norm of `f'' x - f'' y` is the operator norm on `EuclideanSpace ℝ (Fin n)`, which is the spectral norm.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, §2, p. 180 (PDF p. 4), and Assumption 1, (2.1), p. 181 (PDF p. 5)

import Mathlib

open scoped InnerProductSpace

namespace CubicRegNewton.LocalQuad

/-- **Standing assumptions of §2 and Assumption 1.**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, §2, p. 180, and Assumption 1, (2.1), p. 181:
"Let F ⊆ Rⁿ be a closed convex set with non-empty interior. Consider a twice differentiable
function f(x), x ∈ F. Let x0 ∈ int F be a starting point of our iterative schemes. We assume that
the set F is large enough: It contains at least the level set L(f(x0)) ≡ {x ∈ Rⁿ : f(x) ≤ f(x0)}
in its interior." Assumption 1: "The Hessian of function f is Lipschitz continuous on F:
‖f''(x) − f''(y)‖ ≤ L‖x − y‖, ∀x, y ∈ F, (2.1) for some L > 0."

`StandingAssumptions F f f' f'' L x₀` says that `F` is closed and convex, `x₀ ∈ int F`, the level
set `{x ∈ F | f x ≤ f x₀}` lies in `int F`, `f' x` is the gradient and `f'' x` the Hessian of `f`
at every `x ∈ F` (derivatives within `F`), and the Hessian is `L`-Lipschitz on `F` with `L > 0`.

**Formalization Note.**
* Reading 3: "twice differentiable on F" is encoded by giving the gradient `f'` and the Hessian
  `f''` as data, with `HasGradientWithinAt f (f' x) F x` and `HasFDerivWithinAt f' (f'' x) F x` for
  `x ∈ F`. Since `F` is convex with non-empty interior they are uniquely determined on `F`, and
  `f'' x` is symmetric there (a consequence, not an assumption). Values of `f, f', f''` outside
  `F` are unconstrained.
* Reading 4: the level set `L(f(x₀))` is taken inside `F`, `{x | x ∈ F ∧ f x ≤ f x₀}`, since `f` is
  only defined on `F` in the paper.
* Non-empty interior of `F` follows from `x₀ ∈ interior F`.
* `‖f'' x - f'' y‖` is the operator norm on `EuclideanSpace ℝ (Fin n)`, the paper's spectral norm.
-/
structure StandingAssumptions {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) : Prop where
  isClosed : IsClosed F
  convex : Convex ℝ F
  x₀_mem_interior : x₀ ∈ interior F
  levelSet_subset_interior : {x | x ∈ F ∧ f x ≤ f x₀} ⊆ interior F
  hasGradient : ∀ x ∈ F, HasGradientWithinAt f (f' x) F x
  hasHessian : ∀ x ∈ F, HasFDerivWithinAt f' (f'' x) F x
  L_pos : 0 < L
  hessian_lipschitz : ∀ x ∈ F, ∀ y ∈ F, ‖f'' x - f'' y‖ ≤ L * ‖x - y‖

end CubicRegNewton.LocalQuad


