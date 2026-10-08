-- Prove2me | Definitions.Def_AugLagLLC_Penalty_SecondOrder
-- name    : AugLagLLC_Penalty_SecondOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:18.448981+00:00
-- url     : https://prove2.me/theorems/50c92c74-63df-4293-b50e-28257cb40314
-- title:
--   §5.1–§5.2, pp. 11–14 — the Lagrangians L₀ and L, Hessians, LICQ, KKT multipliers, the second-order sufficient conditions and the matrix of Lemma 5.2
-- statement:
--   This file defines the second-order objects of §5 of Andreani, Birgin, Martínez and Schuverdt, on top of the problem data of (2.1).
--
--   1. **Hessian.** For a function $\varphi:\mathbb R^n\to\mathbb R$, $\nabla^2\varphi(x)$ is the derivative of the gradient map $\nabla\varphi$ at $x$.
--   2. **LICQ.** For equality constraints $H_i$ and inequality constraints $G_j$, the linear independence constraint qualification at $x$ says that the gradients $\nabla H_i(x)$ (all $i$) together with $\nabla G_j(x)$ for the active $j$ ($G_j(x)=0$) are linearly independent.
--   3. **Lagrangians.** The Lagrangian of the equality-constrained problem (5.1) is
--   $$L_0(x,\lambda,v)=f(x)+\langle h_1(x),\lambda\rangle+\langle h_2(x),v\rangle,$$
--   and that of (2.1) is $f(x)+\langle h_1(x),\lambda\rangle+\langle g_1(x),\mu\rangle+\langle h_2(x),v\rangle+\langle g_2(x),u\rangle$.
--   4. **Assumption 5 (second-order sufficient condition for (5.1)).** $\lambda_*\in\mathbb R^{m_1}$, $v_*\in\mathbb R^{m_2}$ satisfy $\nabla_x L_0(x_*,\lambda_*,v_*)=0$, and
--   $$\langle z,\nabla^2_{xx}L_0(x_*,\lambda_*,v_*)\,z\rangle>0\quad\text{for all } z\ne0 \text{ with } \nabla h_1(x_*)^Tz=0,\ \nabla h_2(x_*)^Tz=0 .$$
--   5. **The matrix of Lemma 5.2.** For $\pi\in\mathbb R$, the linear map of $\mathbb R^n\times\mathbb R^{m_1}\times\mathbb R^{m_2}$
--   $$(d,a,b)\mapsto\big(\nabla^2_{xx}L_0(x_*,\lambda_*,v_*)d+\nabla h_1(x_*)a+\nabla h_2(x_*)b,\ \ \nabla h_1(x_*)^Td-\pi a,\ \ \nabla h_2(x_*)^Td\big),$$
--   i.e. the block matrix $\begin{pmatrix}\nabla^2_{xx}L_0 & \nabla h_1 & \nabla h_2\\ \nabla h_1^T & -\pi I & 0\\ \nabla h_2^T & 0 & 0\end{pmatrix}$ at $(x_*,\lambda_*,v_*)$.
--   6. **KKT multipliers of (2.1) at $x_*$.** $(\lambda_*,\mu_*,v_*,u_*)$ with $\nabla_x$ of the Lagrangian of (2.1) equal to $0$ at $x_*$, $\mu_*\ge0$, $u_*\ge0$, $[\mu_*]_i=0$ when $[g_1(x_*)]_i<0$ and $[u_*]_i=0$ when $[g_2(x_*)]_i<0$.
--   7. **Assumption 11.** With $T$ the set of $z$ orthogonal to all $\nabla[h_1(x_*)]_i$, $\nabla[h_2(x_*)]_i$ and to $\nabla[g_1(x_*)]_i$, $\nabla[g_2(x_*)]_i$ for the active $i$, the Hessian of the Lagrangian of (2.1) at $(x_*,\lambda_*,\mu_*,v_*,u_*)$ is positive definite on $T$:
--   $$\Big\langle z,\Big[\nabla^2f(x_*)+\sum_i[\lambda_*]_i\nabla^2[h_1(x_*)]_i+\sum_i[\mu_*]_i\nabla^2[g_1(x_*)]_i+\sum_i[v_*]_i\nabla^2[h_2(x_*)]_i+\sum_i[u_*]_i\nabla^2[g_2(x_*)]_i\Big]z\Big\rangle>0,\quad z\in T,\ z\ne0 .$$
--
--   These objects are the hypotheses of Proposition 5.1, Lemmas 5.2 and 5.3 and Theorems 5.4 and 5.5.
--
--   **Formalization Note** The Hessian is `fderiv ℝ (gradient φ) x`, which is the true Hessian only where $\varphi$ is twice differentiable; every statement of the mission that uses it also assumes $C^2$ at $x_*$. Assumption 5 cites Fletcher [25, p. 211]; it is pinned here to its standard equality-constrained form (stationarity of $L_0$ and positive definiteness of $\nabla^2_{xx}L_0$ on the null space of the constraint gradients); feasibility of $x_*$ (Assumption 2) and $C^2$ at $x_*$ (Assumption 4) are stated separately in each theorem. The bracket of Assumption 11 is written as the Hessian of the Lagrangian of (2.1), which equals the bracket under $C^2$ at $x_*$ by linearity of the Hessian. The page never introduces $\lambda_*,\mu_*,v_*,u_*$ for §5.2; they are pinned as KKT multipliers of (2.1) at $x_*$, which LICQ makes unique. LICQ is the linear independence of a family indexed by a sum type, so two equal gradients count as dependent. The block matrix is encoded as a function on $\mathbb R^n\times\mathbb R^{m_1}\times\mathbb R^{m_2}$; it is linear, so injectivity is nonsingularity.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 11, the Lagrangian of (5.1), Assumptions 3 and 5, Lemma 5.2; pp. 13–14, Assumptions 9 and 11

import Mathlib
import Definitions.Def_AugLagLLC_Penalty_Setting

open Filter
open scoped Topology

namespace AugLagLLC.Penalty

/-- The Hessian of `φ : E → ℝ` at `x`, as the derivative of the gradient:
`∇²φ(x) = D(∇φ)(x) : E →L[ℝ] E`. It is the true Hessian whenever `φ` is twice differentiable
at `x`; every statement that uses it also assumes `C²` at `x`. -/
noncomputable def hess {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (φ : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient φ) x

/-- Linear independence constraint qualification at `x` for `H = 0`, `G ≤ 0`: the family of
all equality gradients `∇Hᵢ(x)` together with the gradients `∇Gⱼ(x)` of the active inequality
constraints (`Gⱼ(x) = 0`), indexed by `ι ⊕ {j // Gⱼ(x) = 0}`, is linearly independent. -/
def LICQAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι κ : Type*} (H : ι → E → ℝ) (G : κ → E → ℝ) (x : E) : Prop :=
  LinearIndependent ℝ
    (Sum.elim (fun i : ι => gradient (H i) x) (fun j : {j : κ // G j x = 0} => gradient (G j) x))

namespace Problem

variable {n m1 p1 m2 p2 : ℕ}

/-- The Lagrangian of problem (5.1) (p. 11): `L₀(x, λ, v) = f(x) + ⟨h₁(x), λ⟩ + ⟨h₂(x), v⟩`.
(The inequality constraints, absent in (5.1), do not enter.) -/
noncomputable def lagr0 (P : Problem n m1 p1 m2 p2) (lam : Fin m1 → ℝ) (v : Fin m2 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.f x + ∑ i, lam i * P.h1 i x + ∑ i, v i * P.h2 i x

/-- The Lagrangian of problem (2.1):
`f(x) + ⟨h₁(x), λ⟩ + ⟨g₁(x), μ⟩ + ⟨h₂(x), v⟩ + ⟨g₂(x), u⟩`. Its Hessian in `x` is the bracket of
Assumption 11 (p. 14). -/
noncomputable def lagr (P : Problem n m1 p1 m2 p2) (lam : Fin m1 → ℝ) (mu : Fin p1 → ℝ)
    (v : Fin m2 → ℝ) (u : Fin p2 → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.f x + ∑ i, lam i * P.h1 i x + ∑ i, mu i * P.g1 i x + ∑ i, v i * P.h2 i x
    + ∑ i, u i * P.g2 i x

/-- Assumption 5 (p. 11), Fletcher's second-order sufficient condition [25, p. 211] for the
equality-constrained problem (5.1), with Lagrange multipliers `λ_*`, `v_*`:
(a) `∇ₓL₀(x_*, λ_*, v_*) = 0`;
(b) `⟨z, ∇²ₓₓL₀(x_*, λ_*, v_*) z⟩ > 0` for every `z ≠ 0` with `⟨∇[h₁(x_*)]ᵢ, z⟩ = 0` and
`⟨∇[h₂(x_*)]ᵢ, z⟩ = 0` for all `i`.
Feasibility of `x_*` is Assumption 2 and `C²` at `x_*` is Assumption 4; both are stated
separately. -/
def SOSC0 (P : Problem n m1 p1 m2 p2) (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient (P.lagr0 lamS vS) xs = 0 ∧
    ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      (∀ i, inner ℝ (gradient (P.h1 i) xs) z = 0) →
      (∀ i, inner ℝ (gradient (P.h2 i) xs) z = 0) →
      0 < inner ℝ (hess (P.lagr0 lamS vS) xs z) z

/-- The block linear map of Lemma 5.2 (p. 11) at `x_*`, for `π ∈ ℝ`: on
`ℝⁿ × ℝ^{m₁} × ℝ^{m₂}` it sends `(d, a, b)` to
`(∇²ₓₓL₀(x_*, λ_*, v_*) d + ∇h₁(x_*) a + ∇h₂(x_*) b, ∇h₁(x_*)ᵀ d − π a, ∇h₂(x_*)ᵀ d)`,
i.e. it is the matrix
`[[∇²ₓₓL₀, ∇h₁, ∇h₂], [∇h₁ᵀ, −πI, 0], [∇h₂ᵀ, 0, 0]]`. -/
noncomputable def kktMap (P : Problem n m1 p1 m2 p2) (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (π : ℝ)
    (w : EuclideanSpace ℝ (Fin n) × (Fin m1 → ℝ) × (Fin m2 → ℝ)) :
    EuclideanSpace ℝ (Fin n) × (Fin m1 → ℝ) × (Fin m2 → ℝ) :=
  (hess (P.lagr0 lamS vS) xs w.1 + ∑ i, w.2.1 i • gradient (P.h1 i) xs
      + ∑ i, w.2.2 i • gradient (P.h2 i) xs,
    fun i => inner ℝ (gradient (P.h1 i) xs) w.1 - π * w.2.1 i,
    fun i => inner ℝ (gradient (P.h2 i) xs) w.1)

/-- `(λ_*, μ_*, v_*, u_*)` are KKT multipliers of (2.1) at `x_*`: stationarity of the
Lagrangian, `μ_* ≥ 0`, `u_* ≥ 0`, and complementarity (`[μ_*]ᵢ = 0` if `[g₁(x_*)]ᵢ < 0`,
`[u_*]ᵢ = 0` if `[g₂(x_*)]ᵢ < 0`). Feasibility of `x_*` is stated separately. -/
def IsKKTMult (P : Problem n m1 p1 m2 p2) (lamS : Fin m1 → ℝ) (muS : Fin p1 → ℝ)
    (vS : Fin m2 → ℝ) (uS : Fin p2 → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient (P.lagr lamS muS vS uS) xs = 0 ∧ (∀ i, 0 ≤ muS i) ∧ (∀ i, 0 ≤ uS i) ∧
    (∀ i, P.g1 i xs < 0 → muS i = 0) ∧ ∀ i, P.g2 i xs < 0 → uS i = 0

/-- Assumption 11 (p. 13–14): with `T` the set of `z` orthogonal to every `∇[h₁(x_*)]ᵢ`, every
`∇[h₂(x_*)]ᵢ`, and every `∇[g₁(x_*)]ᵢ`, `∇[g₂(x_*)]ᵢ` of an active constraint, the Hessian of the
Lagrangian at `(x_*, λ_*, μ_*, v_*, u_*)` is positive definite on `T`. -/
def SOSC (P : Problem n m1 p1 m2 p2) (lamS : Fin m1 → ℝ) (muS : Fin p1 → ℝ)
    (vS : Fin m2 → ℝ) (uS : Fin p2 → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
    (∀ i, inner ℝ (gradient (P.h1 i) xs) z = 0) →
    (∀ i, inner ℝ (gradient (P.h2 i) xs) z = 0) →
    (∀ i, P.g1 i xs = 0 → inner ℝ (gradient (P.g1 i) xs) z = 0) →
    (∀ i, P.g2 i xs = 0 → inner ℝ (gradient (P.g2 i) xs) z = 0) →
    0 < inner ℝ (hess (P.lagr lamS muS vS uS) xs z) z

end Problem

end AugLagLLC.Penalty


