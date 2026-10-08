-- Prove2me | Definitions.Def_JaggiFW_PrimalDual_Setting
-- name    : JaggiFW_PrimalDual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:58.780517+00:00
-- url     : https://prove2.me/theorems/f34f0628-561a-473f-bebf-61570feddd59
-- title:
--   (2), (3), Algorithms 1–4 — duality gap, curvature and Frank–Wolfe steps
-- statement:
--   Let $D$ be a subset of a real normed vector space and let $f$ be a real-valued objective. At a feasible point $x$, the **duality gap** is the largest linearized improvement over $D$:
--
--   $$g(x)=\sup_{s\in D} f'(x)(x-s).$$
--
--   The **curvature constant** is the supremum of the scaled error of linearization:
--
--   $$C_f=\sup_{x,s\in D,\;0<\gamma\le1}\frac{2}{\gamma^2}\bigl(f(x+\gamma(s-x))-f(x)-f'(x)(\gamma(s-x))\bigr).$$
--
--   A Frank–Wolfe step chooses an atom $s^{(k)}\in D$. Algorithm 1 minimizes the linear objective exactly and uses $\gamma_k=2/(k+2)$. Algorithm 2 allows additive error $\delta\gamma_k C_f/2$ and uses the same update. Algorithm 3 chooses the step length minimizing $f$ on the segment from $x^{(k)}$ to $s^{(k)}$. Algorithm 4 minimizes $f$ over the convex hull of the initial point and every atom chosen so far.
--
--   These definitions support the paper's primal and duality-gap convergence statements.
--
--   **Formalization Note** The derivative $f'(x)$ represents the pairing with $\nabla f(x)$. The ambient Hilbert space is generalized to a real normed space. The zero step is omitted from the curvature supremum because the displayed quotient is undefined there. Real suprema are used only in later claims with compactness, nonemptiness and bounded-curvature guards. Algorithm 3's oracle tolerance uses the preset $\gamma_k$ before line search. In Algorithm 4, the initial point is its atom $s^{(0)}$.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), https://proceedings.mlr.press/v28/jaggi13.html, PDF pp. 1–3, problem (1), Algorithms 1–4, equations (2)–(3)

import Mathlib

namespace JaggiFW.PrimalDual

/-- Equation (2): the maximal linearized improvement from a feasible point. -/
noncomputable def dualityGap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : Set E) (x : E) : ℝ :=
  sSup ((fun s => fderiv ℝ f x (x - s)) '' D)

/-- The values appearing in the supremum in equation (3), with the undefined zero step omitted. -/
def curvatureSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : Set E) : Set ℝ :=
  {c | ∃ x ∈ D, ∃ s ∈ D, ∃ γ ∈ Set.Ioc (0 : ℝ) 1,
    c = 2 / γ ^ 2 * (f (x + γ • (s - x)) - f x -
      fderiv ℝ f x (γ • (s - x)))}

/-- Equation (3): the curvature constant. Its uses require the defining set to be bounded above. -/
noncomputable def curvatureConst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : Set E) : ℝ :=
  sSup (curvatureSet f D)

/-- The four algorithms on pages 1 and 3. -/
inductive Variant
  | alg1 | alg2 | alg3 | alg4

/-- One step of the chosen Frank–Wolfe variant. `s k` is the atom chosen in step `k`. -/
def IsFWStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : Set E) (δ Cf : ℝ) (v : Variant)
    (x s : ℕ → E) (k : ℕ) : Prop :=
  let γ : ℝ := 2 / ((k : ℝ) + 2)
  s k ∈ D ∧
    (match v with
    | .alg1 => ∀ ŝ ∈ D, fderiv ℝ f (x k) (s k) ≤ fderiv ℝ f (x k) ŝ
    | _ => ∀ ŝ ∈ D, fderiv ℝ f (x k) (s k) ≤
        fderiv ℝ f (x k) ŝ + (1 / 2 : ℝ) * δ * γ * Cf) ∧
    (match v with
    | .alg1 | .alg2 => x (k + 1) = (1 - γ) • x k + γ • s k
    | .alg3 => ∃ γ' ∈ Set.Icc (0 : ℝ) 1,
        x (k + 1) = x k + γ' • (s k - x k) ∧
        ∀ γ'' ∈ Set.Icc (0 : ℝ) 1,
          f (x (k + 1)) ≤ f (x k + γ'' • (s k - x k))
    | .alg4 =>
        let atoms := insert (x 0) (s '' Set.Iic k)
        x (k + 1) ∈ convexHull ℝ atoms ∧
          ∀ y ∈ convexHull ℝ atoms, f (x (k + 1)) ≤ f y)

end JaggiFW.PrimalDual


