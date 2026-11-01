-- Prove2me | Definitions.Def_DoublyOptBandit_LocalNorm
-- name    : DoublyOptBandit_LocalNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:11.697331+00:00
-- url     : https://prove2.me/theorems/6b933713-700c-4873-aa87-d1870dcdc949
-- title:
--   Local norms, Dikin ellipsoid, Newton decrement and Minkowski function of a barrier (§2.1)
-- statement:
--   Let $R:\mathbb R^n\to\mathbb R$ be twice differentiable at $x$. Write $\nabla^2R(x)$ for its Hessian. This module fixes the notions of §2.1 of the paper.
--
--   1. The **local norm** and its dual: $\|h\|_x=\sqrt{h^\top\nabla^2R(x)h}$ and $\|h\|_{x,\star}=\sqrt{h^\top(\nabla^2R(x))^{-1}h}$ for $h\in\mathbb R^n$.
--   2. The **Dikin ellipsoid** at $x$: $W(x)=\{x'\in\mathbb R^n:\|x'-x\|_x\le 1\}$.
--   3. The **Hessian matrix** $\nabla^2R(x)$ in the standard basis, with entries $\nabla^2R(x)[e_j,e_k]$.
--   4. The **Newton decrement** of a function $g$ at $x$: $\lambda(x,g)=\|\nabla g(x)\|_{x,\star}$, computed with the local norm of $g$.
--   5. The **Minkowski function** of a set $X$ with pole $x$ and the scaled set around a point $\bar x$:
--   $$
--   \pi_x(y)=\inf\{t>0:\ x+t^{-1}(y-x)\in X\},\qquad X_\varepsilon=\Big\{x\in\mathbb R^n:\ \pi_{\bar x}(x)\le\frac1{1+\varepsilon}\Big\}.
--   $$
--
--   These objects state the self-concordance facts (Lemmas 2.2, 2.4, 2.5) that the analysis of the bandit mirror descent algorithms relies on.
--
--   **Formalization Note** The Hessian is `iteratedFDeriv ℝ 2 R x`, the same encoding as the published self-concordant barrier definition. The inverse in the dual norm is the matrix inverse, which Lean sets to $0$ for a singular matrix; theorems using it assume a positive definite Hessian. The infimum in $\pi_x$ runs over $t>0$, since $1/t$ is undefined at $t=0$.
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, §2.1, pp.5–6

import Mathlib

open scoped InnerProductSpace

namespace DoublyOptBandit

/-- The **Hessian quadratic form** `h⊤∇²R(x)h` of a function `R : ℝⁿ → ℝ` at `x`
(Ba, Lin, Zhang & Zhou, *Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with
Bandit Feedback*, arXiv:2112.02856v4, §2.1, p.5, the quantity inside the local norm).

**Formalization Note** The Hessian is `iteratedFDeriv ℝ 2 R x` evaluated at `(h, h)`, the same
encoding as the published `EntropicBarrier.Universal.SatisfiesNuBound`. `R` is a total function;
the value is the paper's only at points where `R` is twice differentiable (in the paper, `int X`). -/
noncomputable def hessForm {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ)
    (x h : EuclideanSpace ℝ (Fin m)) : ℝ :=
  iteratedFDeriv ℝ 2 R x (fun _ => h)

/-- The **local norm** `‖h‖ₓ = √(h⊤∇²R(x)h)` induced by `R` at `x`
(arXiv:2112.02856v4, §2.1, p.5: "∥h∥x = √(h⊤∇²R(x)h)"). -/
noncomputable def localNorm {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ)
    (x h : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sqrt (hessForm R x h)

/-- The (closed) **Dikin ellipsoid** `W(x) = {x′ ∈ ℝⁿ : ∥x′ − x∥ₓ ≤ 1}` of `R` at `x`
(arXiv:2112.02856v4, §2.1, p.6: "W(x) = {x′ ∈ Rⁿ : ∥x′ − x∥x ≤ 1}, which is defined at any
x ∈ int(X)"). -/
def dikinEllipsoid {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x' | localNorm R x (x' - x) ≤ 1}

/-- The **Hessian matrix** `∇²R(x)` in the standard basis of `ℝⁿ`: its `(j, k)` entry is
`∇²R(x)[e_j, e_k]` (arXiv:2112.02856v4, §2.1, p.5; used in Algorithm 1 line 4, p.9, and
Algorithm 2 line 5, p.15).

**Formalization Note** Entries are `iteratedFDeriv ℝ 2 R x ![e_j, e_k]`, so that
`h⊤ (hessMat R x) h = hessForm R x h` by bilinearity; the matrix is symmetric wherever `R` is
`C²`. -/
noncomputable def hessMat {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  fun j k => iteratedFDeriv ℝ 2 R x ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]

/-- The **dual local norm** `∥h∥ₓ,⋆ = √(h⊤(∇²R(x))⁻¹h)` (arXiv:2112.02856v4, §2.1, p.5:
"∥h∥x,⋆ = √(h⊤(∇²R(x))⁻¹h) for all h ∈ Rⁿ").

**Formalization Note** `(∇²R(x))⁻¹` is the matrix inverse of `hessMat R x`; Mathlib's inverse
of a singular matrix is `0`, so the value is the paper's only where the Hessian is nonsingular
("the non-degeneracy of R guarantees that both ∥·∥x and ∥·∥x,⋆ are well defined", p.5); every
theorem using it assumes this. -/
noncomputable def dualLocalNorm {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ)
    (x h : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sqrt (dotProduct (WithLp.ofLp h) (Matrix.mulVec (hessMat R x)⁻¹ (WithLp.ofLp h)))

/-- The **Newton decrement** `λ(x, g) := ∥∇g(x)∥ₓ,⋆` of `g` at `x` (arXiv:2112.02856v4, §2.1,
p.6: "the Newton decrement for a self-concordant function g is defined as λ(x, g) :=
∥∇g(x)∥x,⋆ = ∥(∇²g(x))⁻¹∇g(x)∥x"), with the local norms of `g` itself.

**Formalization Note** Defined by the first expression, `√(∇g(x)⊤(∇²g(x))⁻¹∇g(x))`; it equals
the second when `∇²g(x)` is positive definite, which every theorem using it assumes. -/
noncomputable def newtonDecrement {m : ℕ} (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  dualLocalNorm g x (gradient g x)

/-- The **Minkowski function** of `X` with pole `x`:
`πₓ(y) = inf{t ≥ 0 : x + (1/t)(y − x) ∈ X}` (arXiv:2112.02856v4, §2.1, p.6, citing Nesterov and
Nemirovski 1994, p.34).

**Formalization Note** The infimum runs over `t > 0`: at `t = 0` the expression `1/t` is
undefined, and in Lean `0⁻¹ = 0` would put `t = 0` in the set for every `y` with `x ∈ X` and make
`πₓ ≡ 0`. The infimum of the empty set is `0` in Lean; for `X` compact and `x ∈ int X` (the
situation of Lemma 2.4) the set is nonempty. -/
noncomputable def minkowski {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (x y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ x + t⁻¹ • (y - x) ∈ X}

/-- The **scaled set** `X_ε = {x ∈ ℝⁿ : π_x̄(x) ≤ 1/(1 + ε)}` around the point `x̄`
(arXiv:2112.02856v4, §2.1, p.6; there `x̄` is the center of `X` and `ε ∈ (0, 1]`). -/
def scaledSet {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (xbar : EuclideanSpace ℝ (Fin m)) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | minkowski X xbar x ≤ 1 / (1 + ε)}

end DoublyOptBandit


