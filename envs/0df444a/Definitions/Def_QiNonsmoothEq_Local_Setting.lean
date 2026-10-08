-- Prove2me | Definitions.Def_QiNonsmoothEq_Local_Setting
-- name    : QiNonsmoothEq_Local_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:37.489206+00:00
-- url     : https://prove2.me/theorems/1c6bdcc7-810f-4a83-9511-237abb20ba34
-- title:
--   §2–§3, pp. 229–235 — B-differentiability (2.1), semicontinuity (2.4)–(2.5), strong BD-regularity, the ∂_B Newton method (3.2) and the directional Newton method (3.11)–(3.12)
-- statement:
--   Throughout, $F$ is a map between finite-dimensional Euclidean spaces, $F'(x;h)=\lim_{t\downarrow 0}\big(F(x+th)-F(x)\big)/t$ is its one-sided directional derivative, $\partial_B F(x)$ is the B-subdifferential (the set of all limits $\lim_i \nabla F(x_i)$ along sequences $x_i\to x$ of points where $F$ is differentiable) and $\partial F(x)=\operatorname{conv}\partial_B F(x)$ is Clarke's generalized Jacobian. This file fixes the notions of Sections 2 and 3 of Qi (1993).
--
--   1. **Directional differentiability.** $F$ is directionally differentiable at $x$ if $F'(x;h)$ exists for every direction $h$.
--   2. **B-differentiability** (2.1). $F$ is B-differentiable at $x$ if it is directionally differentiable at $x$ and
--   $$\lim_{h\to 0}\frac{F(x+h)-F(x)-F'(x;h)}{\|h\|}=0 .$$
--   3. **Semicontinuity of $F'(\cdot,\cdot)$** (2.4). For every $\varepsilon>0$ there is a neighbourhood $N$ of $x$ such that $\|F'(x+h;h)-F'(x;h)\|\le\varepsilon\|h\|$ whenever $x+h\in N$.
--   4. **Semicontinuity of degree 2** (2.5). There are a constant $L$ and a neighbourhood $N$ of $x$ such that $\|F'(x+h;h)-F'(x;h)\|\le L\|h\|^2$ whenever $x+h\in N$.
--   5. **Nonsingularity.** A linear map $W$ is a two-sided inverse of $V$ if $WV=VW=I$; "$V$ is nonsingular with $\|V^{-1}\|\le c$" means that such a $W$ exists with $\|W\|\le c$.
--   6. **Strong BD-regularity** (p. 233). $F:\mathbb R^n\to\mathbb R^n$ is strongly BD-regular at $x$ if every $V\in\partial_B F(x)$ is nonsingular.
--   7. **A run of the $\partial_B$ Newton method** (3.2) is a sequence $x^0,x^1,\dots$ together with linear maps $V_0,V_1,\dots$ such that for every $k$
--   $$V_k\in\partial_B F(x^k),\qquad V_k\,(x^{k+1}-x^k)=-F(x^k),$$
--   i.e. $x^{k+1}=x^k-V_k^{-1}F(x^k)$ whenever $V_k$ is nonsingular. Every choice of $V_k\in\partial_B F(x^k)$ is admitted.
--   8. **A run of the directional-derivative-based Newton method** (3.11)–(3.12) is a sequence $x^0,x^1,\dots$ such that for every $k$ the directional derivative $F'(x^k;x^{k+1}-x^k)$ exists and $F(x^k)+F'(x^k;x^{k+1}-x^k)=0$, i.e. $x^{k+1}=x^k+d^k$ with $d^k$ a solution of (3.12).
--   9. **The example of Final Remark (6)** (pp. 243–244). On $\mathbb R^2$, $G(u,v)=(-u,\,u^2-v)$, $x_+=(u_+,v_+)$ with $a_+=\max\{a,0\}$, and $F(x)=G(x_+)+x-x_+$.
--
--   These are the objects in which the local convergence theory of the paper is stated: strong BD-regularity is the regularity condition of Theorem 3.1, and the two kinds of runs are the two Newton methods it analyses.
--
--   **Formalization Note** Points of $\mathbb R^n$ are `EuclideanSpace ℝ (Fin n)` (2-norm, spectral operator norm). The general notions are stated for arbitrary real normed spaces. A run of (3.2) is written without an inverse, so nonsingularity of $V_k$ is a conclusion of the theorems, not part of the definition. Semicontinuity (2.4)–(2.5) uses the value `dirDeriv`, which is meaningful only where the directional derivative exists; every statement using these notions assumes directional differentiability on a neighbourhood of $x$, as the page does.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), pp. 229–235 and 243–244, (2.1), (2.4), (2.5), (2.12), strong BD-regularity (p. 233), (3.2), (3.11)–(3.12), Final Remark (6)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), §2, p. 229: `F` is directionally differentiable at `x`, i.e. the one-sided
directional derivative `F'(x; h)` exists for every direction `h`. -/
def DirDiffAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  ∀ h : E, ∃ d : G, NonsmoothNewton.Local.HasDirDerivAt F x h d

/-- Qi (1993), (2.1), p. 229: `F` is B-differentiable at `x` if it is directionally
differentiable at `x` and `(F(x + h) - F(x) - F'(x; h)) / ‖h‖ → 0` as `h → 0`. -/
def BDiffAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  DirDiffAt F x ∧
    Tendsto (fun h : E => ‖h‖⁻¹ * ‖F (x + h) - F x - NonsmoothNewton.Local.dirDeriv F x h‖)
      (𝓝[≠] 0) (𝓝 0)

/-- Qi (1993), (2.4), p. 229: the directional derivative `F'(·, ·)` is semicontinuous at `x`:
for every `ε > 0` there is a neighbourhood `N` of `x` with
`‖F'(x + h; h) - F'(x; h)‖ ≤ ε ‖h‖` whenever `x + h ∈ N`. The page defines it only when `F` is
B-differentiable on a neighbourhood of `x`; every statement using it assumes that. -/
def SemicontAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  ∀ ε > 0, ∃ N ∈ 𝓝 x, ∀ h : E, x + h ∈ N →
    ‖NonsmoothNewton.Local.dirDeriv F (x + h) h - NonsmoothNewton.Local.dirDeriv F x h‖ ≤ ε * ‖h‖

/-- Qi (1993), (2.5), p. 229: `F'(·, ·)` is semicontinuous of degree 2 at `x`: there are a
constant `L` and a neighbourhood `N` of `x` with `‖F'(x + h; h) - F'(x; h)‖ ≤ L ‖h‖²` whenever
`x + h ∈ N`. Used only under B-differentiability on a neighbourhood of `x`. -/
def SemicontDeg2At {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  ∃ L : ℝ, ∃ N ∈ 𝓝 x, ∀ h : E, x + h ∈ N →
    ‖NonsmoothNewton.Local.dirDeriv F (x + h) h - NonsmoothNewton.Local.dirDeriv F x h‖ ≤
      L * ‖h‖ ^ 2

/-- `W` is a two-sided inverse of the linear map `V`; "`V` nonsingular with `‖V⁻¹‖ ≤ c`" is
written `∃ W, IsInverse V W ∧ ‖W‖ ≤ c`. -/
def IsInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V W : E →L[ℝ] E) : Prop :=
  W.comp V = ContinuousLinearMap.id ℝ E ∧ V.comp W = ContinuousLinearMap.id ℝ E

/-- Qi (1993), p. 233: `F` is strongly BD-regular at `x` if every `V ∈ ∂_B F(x)` is
nonsingular. -/
def StronglyBDRegularAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : E) : Prop :=
  ∀ V ∈ NonsmoothNewton.Shared.bJac F x, ∃ W : E →L[ℝ] E, IsInverse V W

/-- A run of the generalized-Jacobian Newton method (3.2), Qi (1993), p. 234:
`x^{k+1} = x^k - V_k⁻¹ F(x^k)` with `V_k ∈ ∂_B F(x^k)`, written without an inverse as
`V_k (x^{k+1} - x^k) = -F(x^k)`. Every choice of `V_k ∈ ∂_B F(x^k)` is allowed. -/
def IsBDNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : ℕ → E) (V : ℕ → E →L[ℝ] E) : Prop :=
  ∀ k, V k ∈ NonsmoothNewton.Shared.bJac F (x k) ∧ V k (x (k + 1) - x k) = -F (x k)

/-- A run of the directional-derivative-based Newton method (3.11)–(3.12), Qi (1993), p. 235:
`x^{k+1} = x^k + d^k` with `F(x^k) + F'(x^k; d^k) = 0`, i.e. `F'(x^k; x^{k+1} - x^k)` exists and
equals `-F(x^k)`. -/
def IsDirNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : ℕ → E) : Prop :=
  ∀ k, NonsmoothNewton.Local.HasDirDerivAt F (x k) (x (k + 1) - x k) (-F (x k))

/-- Final Remark (6), Qi (1993), p. 243: `G : ℝ² → ℝ²`, `G(u, v) = (-u, u² - v)`. -/
noncomputable def remarkG (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-(x 0), (x 0) ^ 2 - x 1]

/-- Final Remark (6), Qi (1993), p. 243: `x₊ = (u₊, v₊)` with `a₊ = max(a, 0)`. -/
noncomputable def posPartVec (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[max (x 0) 0, max (x 1) 0]

/-- Final Remark (6), Qi (1993), p. 244: `F(x) = G(x₊) + x - x₊`. -/
noncomputable def remarkF (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  remarkG (posPartVec x) + x - posPartVec x

end QiNonsmoothEq.Local


