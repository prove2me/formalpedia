-- Prove2me | Definitions.Def_StochFictPlay_DiscreteChoice_Admissible
-- name    : StochFictPlay_DiscreteChoice_Admissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:41:39.427981+00:00
-- url     : https://prove2.me/theorems/e471c35c-ae62-407a-9197-02c054c3d8bb
-- title:
--   Admissible deterministic perturbation $V : \operatorname{int}(\Delta A) \to \mathbb{R}$
-- statement:
--   A **deterministic perturbation** is a function $V : \operatorname{int}(\Delta A) \to \mathbb{R}$ on the interior of the probability simplex; an agent facing payoffs $\pi$ who chooses a mixed action $y$ receives $y \cdot \pi - V(y)$. Since $V$ is defined only on the relative interior of the simplex, its derivatives are taken along the tangent space $\mathbb{R}^n_0 = \{z : \sum_j z_j = 0\}$. Following footnote 3 of the paper, the gradient $\nabla V(y)$ is the vector in $\mathbb{R}^n_0$ with
--
--   $$
--   V(y + hz) = V(y) + (\nabla V(y) \cdot z)\,h + o(h) \qquad \text{for all } z \in \mathbb{R}^n_0 .
--   $$
--
--   Following Fudenberg and Levine (1998), $V$ is **admissible** if
--
--   1. $V$ is twice continuously differentiable along the simplex near every $y \in \operatorname{int}(\Delta A)$;
--   2. for every $y \in \operatorname{int}(\Delta A)$, the second derivative $D^2V(y)$ is positive definite on $\mathbb{R}^n_0$: $D^2V(y)(w, w) > 0$ for every nonzero $w \in \mathbb{R}^n_0$;
--   3. $\|\nabla V(y)\| \to \infty$ as $y$ approaches the boundary of $\Delta A$: for every $M$ there is $\delta > 0$ such that $\|\nabla V(y)\| > M$ whenever $y \in \operatorname{int}(\Delta A)$ has some coordinate $y_i < \delta$.
--
--   The entropy $V(y) = \eta \sum_j y_j \ln y_j$ with $\eta > 0$ is the standard example; it generates the logit choice function.
--
--   **Formalization Note** $V$ is given as a function on all of `Fin n → ℝ`; only its values on the open simplex enter the three conditions. Differentiability is expressed in the chart $z \mapsto V(y + z)$ on the tangent space $\mathbb{R}^n_0$ (a normed subspace of `Fin n → ℝ`), which must be `ContDiffAt ℝ 2` at $0$; $D^2V(y)(w,w)$ is the second Fréchet derivative of that chart at $0$ evaluated at $(w, w)$. The predicate `IsTangentGrad V y g` says $g$ is a gradient in the sense of footnote 3, and condition 3 requires every such $g$ to have norm above $M$. The norm is the sup norm on $\mathbb{R}^n$; all norms on $\mathbb{R}^n$ are equivalent, so the blow-up condition does not depend on the choice. Approach to the boundary is measured by the smallest coordinate; the boundary is compact, so this uniform form is the paper's limit.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 5, §2 (definition of an admissible deterministic perturbation) and p. 7, footnote 3 (definition of ∇V)

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex

namespace StochFictPlay.DiscreteChoice

/-- The restriction of `V : ℝⁿ → ℝ` to the affine plane `{∑ⱼ yⱼ = 1}` through `y`, written in
the coordinates of the tangent space: `z ↦ V (y + z)` for `z ∈ R₀ⁿ`. -/
def planeRestrict {n : ℕ} (V : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : tangentSpace n → ℝ :=
  fun z => V (y + (z : Fin n → ℝ))

/-- `g` is the gradient `∇V(y)` of footnote 3 of Hofbauer–Sandholm (2002), p. 7: the vector
`g ∈ R₀ⁿ` with `V(y + hz) = V(y) + (g · z) h + o(h)` for every direction `z ∈ R₀ⁿ`. -/
def IsTangentGrad {n : ℕ} (V : (Fin n → ℝ) → ℝ) (y g : Fin n → ℝ) : Prop :=
  (∑ i, g i = 0) ∧
    ∀ z : Fin n → ℝ, ∑ i, z i = 0 → HasDerivAt (fun h : ℝ => V (y + h • z)) (g ⬝ᵥ z) 0

/-- An **admissible deterministic perturbation** (Hofbauer–Sandholm (2002), p. 5, following
Fudenberg–Levine 1998). Only the values of `V` on `int(ΔA)` matter. The conditions are:
1. `V` is twice continuously differentiable along the simplex at every interior point;
2. the second derivative `D²V(y)` is positive definite on the tangent space `R₀ⁿ`;
3. `‖∇V(y)‖ → ∞` as `y` approaches the boundary of `ΔA`: for every `M` there is `δ > 0` such
   that every tangent gradient at an interior `y` with some coordinate below `δ` has norm `> M`. -/
def IsAdmissible {n : ℕ} (V : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ y ∈ openSimplex n, ContDiffAt ℝ 2 (planeRestrict V y) 0) ∧
  (∀ y ∈ openSimplex n, ∀ w : tangentSpace n, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (planeRestrict V y)) 0 w w) ∧
  (∀ M : ℝ, ∃ δ > 0, ∀ y ∈ openSimplex n, (∃ i, y i < δ) →
      ∀ g, IsTangentGrad V y g → M < ‖g‖)

end StochFictPlay.DiscreteChoice


