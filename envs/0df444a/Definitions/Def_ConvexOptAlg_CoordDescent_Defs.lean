-- Prove2me | Definitions.Def_ConvexOptAlg_CoordDescent_Defs
-- name    : ConvexOptAlg_CoordDescent_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:46:15.661425+00:00
-- url     : https://prove2.me/theorems/5e481b1d-d7d0-40c4-a3b8-efe372b8c5c4
-- title:
--   §6.4.1, p. 339 — coordinate-wise smoothness, weighted norms ‖·‖_[γ], ‖·‖*_[γ], strong convexity, p_γ and RCD(γ)
-- statement:
--   These are the objects of §6.4 (random coordinate descent). Throughout, $\mathbb R^n$ has coordinates $x=(x_1,\dots,x_n)$, $e_i$ is the $i$-th standard basis vector, $f:\mathbb R^n\to\mathbb R$ is differentiable, and $\nabla_i f(x)=\frac{\partial f}{\partial x_i}(x)$. Let $\beta_1,\dots,\beta_n>0$.
--
--   1. **Coordinate-wise smoothness.** $f$ is *directionally smooth with constants $\beta_1,\dots,\beta_n$* if for every $i\in[n]$, $x\in\mathbb R^n$ and $u\in\mathbb R$,
--   $$|\nabla_i f(x+ue_i)-\nabla_i f(x)|\le\beta_i|u|.$$
--   Equivalently, for every $i$ and $x$, the one-variable function $u\mapsto f(x+ue_i)$ is $\beta_i$-smooth.
--   2. **Weighted norms.** For a real exponent $c$,
--   $$\|x\|_{[c]}=\sqrt{\sum_{i=1}^n\beta_i^{c}x_i^2},\qquad \|x\|^*_{[c]}=\sqrt{\sum_{i=1}^n\frac{1}{\beta_i^{c}}x_i^2}.$$
--   3. **Strong convexity.** For a norm $\|\cdot\|$ and $\alpha\in\mathbb R$, $f$ is *$\alpha$-strongly convex w.r.t. $\|\cdot\|$* if for all $x,y$
--   $$f(x)-f(y)\le\nabla f(x)^\top(x-y)-\frac{\alpha}{2}\|x-y\|^2.$$
--   This is defined both for an arbitrary norm on a finite-dimensional space (with $\nabla f(x)$ the derivative, a linear functional) and for the weighted norm $\|\cdot\|_{[c]}$ on $\mathbb R^n$.
--   4. **Sampling distribution and condition number.** For $\gamma\ge0$,
--   $$p_\gamma(i)=\frac{\beta_i^\gamma}{\sum_{j=1}^n\beta_j^\gamma},\qquad \kappa_\gamma=\frac{\sum_{i=1}^n\beta_i^\gamma}{\alpha}.$$
--   5. **RCD(γ).** From $x_1\in\mathbb R^n$, with coordinates $i_1,i_2,\dots$ drawn independently from $p_\gamma$,
--   $$x_{s+1}=x_s-\frac{1}{\beta_{i_s}}\nabla_{i_s}f(x_s)\,e_{i_s}.$$
--   The iterate $x_{t+1}$ is a function of $(i_1,\dots,i_t)$, and its expectation is the finite sum $\mathbb E\,F(i_1,\dots,i_t)=\sum_{(i_1,\dots,i_t)\in[n]^t}\prod_{s=1}^t p_\gamma(i_s)\,F(i_1,\dots,i_t)$.
--
--   These definitions set up Nesterov's (2012) analysis of random coordinate descent with non-uniform sampling: smoothness is measured coordinate by coordinate, and the weighted norms are the geometry in which the rates are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$ at every $x$ (`HasGradientAt`), so $\nabla_i f(x)=g(x)_i$. Coordinate-wise smoothness is the inequality of §6.4.1 together with the gradient hypothesis; given the gradient, it is equivalent to the form "$u\mapsto f(x+ue_i)$ is $\beta_i$-smooth" used in Theorems 6.7–6.8, since that map has derivative $u\mapsto\nabla_i f(x+ue_i)$. Powers $\beta_i^c$ are real powers (`Real.rpow`); the theorems assume $\beta_i>0$. For an arbitrary norm the gradient is the Fréchet derivative $f'(x):E\to\mathbb R$ and $\nabla f(x)^\top(x-y)$ is $f'(x)(x-y)$. The algorithm is a function of the drawn coordinates (`rcdIter`, where `rcdIter β g x₁ t idx` is $x_{t+1}$ with $i_s=$ `idx (s-1)`), and the expectation over $t$ i.i.d. draws from $p_\gamma$ is the finite weighted sum `rcdExpect`; no measure theory is involved.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, §6.4 preamble, p. 338; §6.4.1, p. 339 (directional smoothness, RCD(γ), p_γ, ‖·‖_[γ], ‖·‖*_[γ]); Theorem 6.8, p. 341 (κ_γ, strong convexity w.r.t. ‖·‖_[1−γ]); (3.13), p. 276

import Mathlib

namespace ConvexOptAlg.CoordDescent

/-- α-strong convexity with respect to an arbitrary norm (Bubeck, arXiv:1405.4980v2, (3.13), p. 276,
with the Euclidean norm replaced by the norm `‖·‖` of `E`, as in Lemma 6.9, p. 341):
`f` is differentiable with derivative `f' x : E →L[ℝ] ℝ` at every `x` (the book's `∇f(x)`, acting
by `∇f(x)⊤y = f' x y`), and `f(x) − f(y) ≤ ∇f(x)⊤(x − y) − (α/2)‖x − y‖²` for all `x, y`. -/
def IsStronglyConvexNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (f' : E → (E →L[ℝ] ℝ)) (α : ℝ) : Prop :=
  (∀ x, HasFDerivAt f (f' x) x) ∧ ∀ x y, f x - f y ≤ f' x (x - y) - α / 2 * ‖x - y‖ ^ 2

/-- The weighted norm `‖x‖_[c] = √(Σᵢ βᵢ^c xᵢ²)` on `ℝⁿ` (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 339,
with `c` in place of the book's `γ`); `βᵢ^c` is the real power `Real.rpow` (the book has `βᵢ > 0`). -/
noncomputable def wnorm {n : ℕ} (β : Fin n → ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ i, β i ^ c * x i ^ 2)

/-- The dual weighted norm `‖x‖*_[c] = √(Σᵢ xᵢ²/βᵢ^c)` (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 339). -/
noncomputable def wnormDual {n : ℕ} (β : Fin n → ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2 / β i ^ c)

/-- α-strong convexity with respect to the weighted norm `‖·‖_[c]` (Bubeck, arXiv:1405.4980v2,
(3.13), p. 276, with the norm `‖·‖_[c]`, as in Theorem 6.8, p. 341, where `c = 1 − γ`):
`f : ℝⁿ → ℝ` has gradient `g x = ∇f(x)` at every `x`, and
`f(x) − f(y) ≤ ∇f(x)⊤(x − y) − (α/2)‖x − y‖²_[c]` for all `x, y`. -/
def IsStronglyConvexWNorm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (c α : ℝ) : Prop :=
  (∀ x, HasGradientAt f (g x) x) ∧
    ∀ x y, f x - f y ≤ (∑ i, g x i * (x i - y i)) - α / 2 * wnorm β c (x - y) ^ 2

/-- Coordinate-wise (directional) smoothness (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 339):
`f : ℝⁿ → ℝ` has gradient `g x = ∇f(x)` at every `x` (so `∇ᵢ f(x) = ∂f/∂xᵢ(x) = g x i`), and for
every `i ∈ [n]`, `x ∈ ℝⁿ`, `u ∈ ℝ`, `|∇ᵢ f(x + u eᵢ) − ∇ᵢ f(x)| ≤ βᵢ |u|`, where `eᵢ` is the `i`-th
standard basis vector. Given the gradient, this is the same as "`u ↦ f(x + u eᵢ)` is βᵢ-smooth for
every `i` and `x`" (the form of Theorems 6.7 and 6.8), since that map has derivative
`u ↦ ∇ᵢ f(x + u eᵢ)`. -/
def IsCoordSmooth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) : Prop :=
  (∀ x, HasGradientAt f (g x) x) ∧
    ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
      |g (x + u • EuclideanSpace.single i 1) i - g x i| ≤ β i * |u|

/-- The sampling distribution of RCD(γ) (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 339):
`p_γ(i) = βᵢ^γ / Σⱼ βⱼ^γ`. -/
noncomputable def pGamma {n : ℕ} (β : Fin n → ℝ) (γ : ℝ) (i : Fin n) : ℝ :=
  β i ^ γ / ∑ j, β j ^ γ

/-- The condition number `κ_γ = (Σᵢ βᵢ^γ)/α` of Theorem 6.8 (Bubeck, arXiv:1405.4980v2, p. 341). -/
noncomputable def kappa {n : ℕ} (β : Fin n → ℝ) (γ α : ℝ) : ℝ :=
  (∑ i, β i ^ γ) / α

/-- One step of RCD(γ) along coordinate `i` (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 339):
`x − (1/βᵢ) ∇ᵢ f(x) eᵢ`, with `∇ᵢ f(x) = g x i`. -/
noncomputable def rcdStep {n : ℕ} (β : Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  x - (1 / β i * g x i) • EuclideanSpace.single i 1

/-- The RCD(γ) iterate after `t` steps (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 339), as a function of
the drawn coordinates: `rcdIter β g x₁ t idx` is the book's `x_{t+1}` when the coordinates drawn are
`i₁ = idx 0, …, i_t = idx (t − 1)`, i.e. `x_{s+1} = x_s − (1/β_{i_s}) ∇_{i_s} f(x_s) e_{i_s}`
for `s = 1, …, t`, starting from `x₁`. -/
noncomputable def rcdIter {n : ℕ} (β : Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₁ : EuclideanSpace ℝ (Fin n)) : (t : ℕ) → (Fin t → Fin n) → EuclideanSpace ℝ (Fin n)
  | 0, _ => x₁
  | t + 1, idx => rcdStep β g (rcdIter β g x₁ t (Fin.init idx)) (idx (Fin.last t))

/-- Expectation over `t` coordinates drawn independently from `p_γ` (Bubeck, arXiv:1405.4980v2,
§6.4.1, p. 339): `E[F(i₁, …, i_t)] = Σ_{idx} (Π_s p_γ(idx s)) F(idx)`, the sum running over all
`idx : Fin t → Fin n` (`idx s` is the book's `i_{s+1}`). -/
noncomputable def rcdExpect {n : ℕ} (β : Fin n → ℝ) (γ : ℝ) (t : ℕ)
    (F : (Fin t → Fin n) → ℝ) : ℝ :=
  ∑ idx : Fin t → Fin n, (∏ s, pGamma β γ (idx s)) * F idx

end ConvexOptAlg.CoordDescent


