-- Prove2me | Definitions.Def_StrictCQ_AGP_LAGP
-- name    : StrictCQ_AGP_LAGP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:45.268843+00:00
-- url     : https://prove2.me/theorems/f237c81c-ad09-464e-9317-fa77f54de88c
-- title:
--   (4.27), (4.28), Definition 4.4, p. 12 — Ω_L, Ω_NL(x, −∞), the LAGP condition and LAGP-regularity
-- statement:
--   Let $h,g$ be the constraint data of problem (1.1). A constraint is **linear** if its function is affine, $\varphi(x)=\langle a,x\rangle+b$. Let $I_1$ and $J_1$ be the indices of the non-linear equality and inequality constraints.
--
--   1. $\Omega_L$ is the set defined by all the linear constraints: $h_i(x)=0$ for $i\notin I_1$ and $g_j(x)\le0$ for $j\notin J_1$.
--   2. **(4.27)** For $x\in\mathbb R^n$,
--   $$\Omega_{NL}(x,-\infty)=\left\{z:\ \begin{array}{ll}\langle\nabla h_i(x),z-x\rangle=0, & i\in I_1\\ \langle\nabla g_j(x),z-x\rangle\le0, & \text{if } 0\le g_j(x),\ j\in J_1\\ g_j(x)+\langle\nabla g_j(x),z-x\rangle\le0, & \text{if } g_j(x)<0,\ j\in J_1\end{array}\right\}.$$
--   3. **LAGP (4.28).** $x^*$ satisfies LAGP for $f$ if there is a sequence $x^k\in\Omega_L$ with $x^k\to x^*$ and $P_{\Omega_{NL}(x^k,-\infty)\cap\Omega_L}(x^k-\nabla f(x^k))-x^k\to0$.
--   4. **LAGP-regularity (Definition 4.4).** The map $(x,\varepsilon)\rightrightarrows N_{\Omega_{NL}(x,-\infty)\cap\Omega_L}(x+\varepsilon)$ is outer semicontinuous at $(x^*,0)$ relative to $\Omega_L\times\mathbb R^n$:
--   $$\limsup_{(x,\varepsilon)\to(x^*,0),\ x\in\Omega_L}N_{\Omega_{NL}(x,-\infty)\cap\Omega_L}(x+\varepsilon)\subset N_{\Omega_{NL}(x^*,-\infty)\cap\Omega_L}(x^*).$$
--
--   LAGP is the variant of AGP that keeps the linear constraints exact; Theorem 4.6 is its analogue of Theorem 4.2.
--
--   **Formalization Note** Which constraints are linear is determined by the data (affine functions), not chosen. The paper writes "relatively to $\Omega_L\times\mathbb R^m$"; the second factor is the space of perturbations $\varepsilon\in\mathbb R^n$, and the formalization restricts only $x$ to $\Omega_L$. Projections are a predicate, as for AGP. The equality with $L_\Omega(x^*)^\circ$ appended to Definition 4.4 is a separate theorem.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 12, (4.27), (4.28), Definition 4.4

import Mathlib
import Definitions.Def_StrictCQ_AGP_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

variable {n m p : ℕ}

/-- A constraint function is linear (affine): `φ(x) = ⟨a, x⟩ + b`. -/
def IsAffine (φ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), ∀ x, φ x = ⟪a, x⟫_ℝ + b

/-- `Ω_L`: the set defined by all the linear constraints of (1.1). -/
def Constraints.linPart (C : Constraints n m p) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, IsAffine (C.h i) → C.h i x = 0) ∧ ∀ j, IsAffine (C.g j) → C.g j x ≤ 0}

/-- `Ω_NL(x, -∞)` of (4.27): the linearization at `x` of the non-linear constraints
(`I₁ = {i | hᵢ not affine}`, `J₁ = {j | gⱼ not affine}`). -/
def Constraints.nonlinSet (C : Constraints n m p) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (∀ i, ¬ IsAffine (C.h i) → ⟪gradient (C.h i) x, z - x⟫_ℝ = 0) ∧
    (∀ j, ¬ IsAffine (C.g j) → 0 ≤ C.g j x → ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0) ∧
    (∀ j, ¬ IsAffine (C.g j) → C.g j x < 0 →
      C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0)}

/-- LAGP at `xs` for `f`, (4.28): there are `xᵏ ∈ Ω_L`, `xᵏ → xs`, and projections
`yᵏ = P_{Ω_NL(xᵏ,-∞) ∩ Ω_L}(xᵏ - ∇f(xᵏ))` with `yᵏ - xᵏ → 0`. -/
def Constraints.LAGP (C : Constraints n m p) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ x y : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, x k ∈ C.linPart) ∧ Tendsto x atTop (𝓝 xs) ∧
    (∀ k, IsProj (C.nonlinSet (x k) ∩ C.linPart) (x k - gradient f (x k)) (y k)) ∧
    Tendsto (fun k => y k - x k) atTop (𝓝 0)

/-- LAGP-regularity, Definition 4.4: `(x, ε) ↦ N_{Ω_NL(x,-∞) ∩ Ω_L}(x + ε)` is outer
semicontinuous at `(xs, 0)` relative to `Ω_L × ℝⁿ`. -/
def Constraints.LAGPRegular (C : Constraints n m p) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  outerLimitWithin
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        normalCone (C.nonlinSet q.1 ∩ C.linPart) (q.1 + q.2))
      {q | q.1 ∈ C.linPart} (xs, 0) ⊆
    normalCone (C.nonlinSet xs ∩ C.linPart) xs

end StrictCQ.AGP


