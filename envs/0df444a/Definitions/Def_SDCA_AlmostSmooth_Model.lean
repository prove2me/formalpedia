-- Prove2me | Definitions.Def_SDCA_AlmostSmooth_Model
-- name    : SDCA_AlmostSmooth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:37.295237+00:00
-- url     : https://prove2.me/theorems/378ae47f-b767-4148-a1a1-63a2a614003a
-- title:
--   Primal (1), dual (2), $w(\alpha)$ (3), the SDCA run, the refined dual strong convexity (4) and inequality (5), and $N(u)$
-- statement:
--   Fix data $x_1,\dots,x_n\in\mathbb R^d$ (with the Euclidean norm), scalar losses $\varphi_1,\dots,\varphi_n:\mathbb R\to\mathbb R$ and a regularization parameter $\lambda>0$. This definition file introduces the objects of regularized loss minimization and of Procedure SDCA.
--
--   1. The **primal vector** of a dual variable $\alpha\in\mathbb R^n$ is $w(\alpha)=\frac{1}{\lambda n}\sum_{i=1}^n\alpha_i x_i$ (eq. (3)).
--   2. The **primal objective** (1) is $P(w)=\frac1n\sum_{i=1}^n\varphi_i(w^\top x_i)+\frac\lambda2\|w\|^2$.
--   3. The **dual objective** (2) is
--   $$
--   D(\alpha)=\frac1n\sum_{i=1}^n-\varphi_i^*(-\alpha_i)-\frac\lambda2\Bigl\|\frac{1}{\lambda n}\sum_{i=1}^n\alpha_i x_i\Bigr\|^2\in[-\infty,+\infty),
--   $$
--   where $\varphi_i^*$ is the convex conjugate. A dual variable is **feasible** if every $\varphi_i^*(-\alpha_i)$ is finite, i.e. $D(\alpha)>-\infty$.
--   4. **One SDCA step** on coordinate $i$ at the dual point $\alpha$ chooses $\Delta\alpha_i$ maximizing
--   $$
--   \delta\mapsto-\varphi_i^*\bigl(-(\alpha_i+\delta)\bigr)-\frac{\lambda n}{2}\bigl\|w(\alpha)+(\lambda n)^{-1}\delta x_i\bigr\|^2 ,
--   $$
--   and sets $\alpha\leftarrow\alpha+\Delta\alpha_i e_i$. A step rule $\Delta$ (giving the increment $\Delta(\alpha,i)$) is an **SDCA step** if $\Delta(\alpha,i)$ maximizes this objective for every $\alpha$ and $i$.
--   5. The **SDCA run** from $\alpha^{(0)}=0$: if the coordinates chosen at iterations $1,2,\dots$ are $j_1,j_2,\dots$, then $\alpha^{(t)}$ is obtained from $\alpha^{(t-1)}$ by one SDCA step on coordinate $j_t$. The primal iterate is $w^{(t)}=w(\alpha^{(t)})$.
--   6. **Definition 2, (4).** Functions $\gamma_i(\cdot)\ge0$ satisfy (4) if, for all dual values $a,b$ and every $u\in\partial\varphi_i^*(-b)$,
--   $$
--   \varphi_i^*(-a)-\varphi_i^*(-b)+u(a-b)\ge\gamma_i(u)\,|a-b|^2 .
--   $$
--   7. **Inequality (5)** with constants $\gamma_1,\dots,\gamma_n$ at the dual point $\alpha^*$, with $w^*=w(\alpha^*)$: for every feasible $\alpha$,
--   $$
--   D(\alpha^*)-D(\alpha)\ge\frac1n\sum_{i=1}^n\gamma_i|\alpha_i-\alpha_i^*|^2+\frac\lambda2\|w(\alpha)-w^*\|^2 .
--   $$
--   8. $N(u)=\#\{i:\gamma_i<u\}$, the number of coordinates whose constant is strictly below $u$.
--
--   These are the objects in which Proposition 1, Lemmas 2, 3, 5, 6 and Theorem 5 of the paper are stated.
--
--   **Formalization Note** $D$ takes values in `EReal` with real coefficients coerced; it is $-\infty$ exactly at infeasible points and never $+\infty$. The SDCA step is modelled as a map $\Delta:\mathbb R^n\times\{1,\dots,n\}\to\mathbb R$ together with the predicate that it is an argmax of the coordinate objective, not by a choice function. The run is a left fold of the steps over the list of the first $t$ chosen coordinates (indices $0$-based, $j_{t}$ is `js (t-1)`). Inequalities (4) and (5) are stated in `EReal`; (5) quantifies over feasible $\alpha$ only, and its $w^*$ is $w(\alpha^*)$, the vector that the first-order facts of p. 12 identify with the primal optimum.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, pp. 1–2 ((1), (2), (3)), p. 5 (Procedure SDCA), p. 8 (Definition 2, (4), (5)), p. 9 (Theorem 5, N(u)), p. 18 (feasible dual variable)

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_conj
import Definitions.Def_SDCA_Lipschitz_Model
import Definitions.Def_SDCA_Smooth_Model

namespace SDCA.AlmostSmooth

open scoped InnerProductSpace

/-- A feasible dual variable (p. 18): every `φᵢ*(−αᵢ)` is finite, equivalently `D(α) > −∞`. -/
def Feasible {n : ℕ} (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) : Prop :=
  ∀ i, SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤

/-- Definition 2, (4) (p. 8): the functions `γᵢ(·) ≥ 0` satisfy, for all dual values `a, b` and
every `u ∈ ∂φᵢ*(−b)`, `φᵢ*(−a) − φᵢ*(−b) + u(a − b) ≥ γᵢ(u)|a − b|²` (in `EReal`; the left side
is `+∞` when `φᵢ*(−a) = +∞`). -/
def RefinedDualStrongConvexity {n : ℕ} (φ : Fin n → ℝ → ℝ) (γfun : Fin n → ℝ → ℝ) : Prop :=
  (∀ i u, 0 ≤ γfun i u) ∧
    ∀ (i : Fin n) (a b u : ℝ), IsConjSubgrad (φ i) (-b) u →
      ((γfun i u * |a - b| ^ 2 : ℝ) : EReal) ≤
        SDCA.Lipschitz.conj (φ i) (-a) - SDCA.Lipschitz.conj (φ i) (-b) + ((u * (a - b) : ℝ) : EReal)

/-- The dual strong convexity inequality (5) (p. 8) with constants `γᵢ` and `w* = w(α*)`: for every
feasible dual variable `α`,
`D(α*) − D(α) ≥ (1/n) ∑ᵢ γᵢ |αᵢ − α*ᵢ|² + (λ/2)‖w(α) − w(α*)‖²` (in `EReal`). -/
def DualStrongConvexity {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (γ : Fin n → ℝ) (αstar : Fin n → ℝ) : Prop :=
  ∀ α : Fin n → ℝ, Feasible φ α →
    (((1 / (n : ℝ)) * ∑ i, γ i * |α i - αstar i| ^ 2 +
        lam / 2 * ‖SDCA.Smooth.wOf lam x α - SDCA.Smooth.wOf lam x αstar‖ ^ 2 : ℝ) : EReal) ≤
      SDCA.Smooth.dual lam x φ αstar - SDCA.Smooth.dual lam x φ α

/-- `N(u) = #{i : γᵢ < u}` (Theorem 5, p. 9). -/
noncomputable def countBelow {n : ℕ} (γ : Fin n → ℝ) (u : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => γ i < u)).card

end SDCA.AlmostSmooth


