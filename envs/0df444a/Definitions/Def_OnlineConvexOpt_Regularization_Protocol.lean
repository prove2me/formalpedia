-- Prove2me | Definitions.Def_OnlineConvexOpt_Regularization_Protocol
-- name    : OnlineConvexOpt_Regularization_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:35:09.358975+00:00
-- url     : https://prove2.me/theorems/1f5709a2-68d1-422a-9afc-4d50216793e7
-- title:
--   RFTL/OMD protocol: Bregman divergence, local dual norm, D_R, and algorithm runs
-- statement:
--   This item collects the shared machinery of Chapter 5 ("Regularization"): the Bregman divergence of a regularizer, the "local" dual norm it induces (Definition 5.1), the R-diameter $D_R^2$ of the decision set, the auxiliary functions $g_t$ used in the RFTL analysis, and the predicates that a decision/gradient sequence is a run of the RFTL algorithm (Algorithm 13) or of the agile Online Mirror Descent algorithm (Algorithm 14, agile version).
--
--   **Bregman divergence.** For a regularizer $R : E \to \mathbb{R}$ with gradient map $\mathrm{gradR}$, $$B_R(x\|y) = R(x) - R(y) - \langle \mathrm{gradR}(y), x - y\rangle,$$ exactly Definition 5.1's formula, the gap between $R(x)$ and $R$'s first-order Taylor approximation at $y$.
--
--   **Local dual norm.** `IsLocalDualNormSq R gradR x y v nsq` says $nsq$ is the squared local dual norm $\|v\|^{*2}_{x,y}$ of Definition 5.1: there is a point $z = ax + (1-a)y$ on the segment $[x,y]$ ($a \in [0,1]$) at which the second Fréchet derivative of $\mathrm{gradR}$ (the Hessian $\nabla^2 R(z)$) is a self-adjoint, positive-definite operator $H$, the Bregman divergence between $x$ and $y$ equals $\tfrac12\|x-y\|_H^2$ (the mean-value form of Definition 5.1, using the quadratic form $\|w\|_H^2 = \langle w, Hw\rangle$), and $nsq$ is the squared dual norm of $v$ with respect to $H$, $\|v\|^{*2}_H = \|v\|^2_{H^{-1}}$ (the book's $\|y\|^*_A = \|y\|_{A^{-1}}$, p. 72).
--
--   **R-diameter.** $D_R^2 = \sup_{x,y \in K} (R(x) - R(y))$, the book's $D_R^2 = \max_{x,y\in K}\{R(x)-R(y)\}$.
--
--   **The auxiliary functions $g_t$.** $g_0(x) = \tfrac1\eta R(x)$ and, for $n \ge 1$, $g_n(x) = \langle \nabla_n, x\rangle$ — the functions Lemma 5.3's proof introduces, needed to state Lemma 5.4 verbatim.
--
--   **RFTL run.** `IsRFTLRun K R η f x grad` says $(x, \mathrm{grad})$ is a run of Algorithm 13: $x_0$ minimizes $R$ over $K$ (the book's $x_1 = \arg\min_{x\in K} R(x)$); at every round $t$, $\mathrm{grad}\ t$ is the gradient of $f_t$ at $x_t$; and $x_{t+1}$ minimizes over $K$ the function $y \mapsto \eta \sum_{s \le t} \langle \mathrm{grad}\ s, y\rangle + R(y)$ (the book's $x_{t+2} = \arg\min_{x\in K}\{\eta\sum_{s=1}^{t+1}\nabla_s^\top x + R(x)\}$, under this chapter's 0-indexed shift: round $t \in \mathbb{N}$ is the book's round $t+1$).
--
--   **Agile OMD run.** `IsOMDAgileRun K R gradR η f x grad y` says $(x,\mathrm{grad},y)$ is a run of Algorithm 14's agile version: $\mathrm{gradR}(y_0) = 0$ and $x_0$ minimizes $B_R(\cdot\|y_0)$ over $K$ (the book's $\nabla R(y_1)=0$, $x_1 = \arg\min_{x\in K} B_R(x\|y_1)$); at every round $t$, $\mathrm{grad}\ t$ is the gradient of $f_t$ at $x_t$; the dual point updates by $\mathrm{gradR}(y_{t+1}) = \mathrm{gradR}(x_t) - \eta\,\mathrm{grad}_t$; and $x_{t+1}$ minimizes $B_R(\cdot\|y_{t+1})$ over $K$.
--
--   **Formalization Note.** All declarations live over a real inner product space $E$ that is complete (a real Hilbert space), matching Chapter III's convention. The projection-style predicates are relational (`IsArgMinOn`), not functional, since Mathlib has no canonical argmin operator for a general set. The "local" Hessian at an intermediate point is represented existentially via `HasFDerivAt` of the gradient map, since Mathlib has no dedicated second-derivative/Hessian type; `quadForm` and `IsArgMinOn` mirror the already-published `OnlineConvexOpt.FirstOrder.Protocol`'s `IsMetricProjection` and `OnlineConvexOpt.SecondOrder`'s `quadForm` (redeclared here, since that chapter's mission is not yet published and a draft cannot import another draft's definitions).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 72-75, Definition 5.1 and Algorithms 13-14 (PDF p. 94-97, 100)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `IsArgMinOn h K p`: `p` is a minimizer of `h` over `K`, i.e. `p ∈ K` and `h p ≤ h y` for
every `y ∈ K`. Used for both `x_1 = arg min_{x ∈ K} R(x)` and the RFTL/OMD update rules
(Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Algorithms
13/14, p. 74/78, PDF p. 96/100). -/
def IsArgMinOn (h : E → ℝ) (K : Set E) (p : E) : Prop :=
  p ∈ K ∧ ∀ y ∈ K, h p ≤ h y

/-- The squared (semi)norm induced by an operator `A : E →L[ℝ] E`, `‖v‖²_A = ⟪v, A v⟫`, as in
`OnlineConvexOpt.SecondOrder.quadForm` (redeclared here since that chapter's mission is not yet
published and a draft cannot import another draft's definitions). -/
noncomputable def quadForm (A : E →L[ℝ] E) (v : E) : ℝ := inner ℝ v (A v)

/-- The Bregman divergence of `R` with gradient map `gradR`, between `x` and `y`: the gap
between `R x` and the first-order Taylor approximation of `R` at `y` (Definition 5.1, book
p. 73, PDF p. 95): `B_R(x‖y) = R(x) - R(y) - ∇R(y)^⊤(x - y)`. -/
def BregmanDivergence (R : E → ℝ) (gradR : E → E) (x y : E) : ℝ :=
  R x - R y - ⟪gradR y, x - y⟫_ℝ

/-- `IsLocalDualNormSq R gradR x y v nsq` holds when `nsq` is the squared "local" dual norm
`‖v‖*²_{x,y}` of book p. 73, PDF p. 95: there is a point `z` on the segment `[x, y]` (written
`a • x + (1 - a) • y` for some `a ∈ [0,1]`) at which the second Fréchet derivative of `R`'s
gradient map is a self-adjoint, positive-definite operator `H` (the book's `∇²R(z)`), the
Bregman divergence between `x` and `y` equals the squared `H`-norm of `x - y` scaled by `1/2`
(the mean-value form of Definition 5.1, `B_R(x‖y) = (1/2)‖x-y‖²_z`), and `nsq` is the squared
`H`-dual norm of `v` (the book's `‖v‖*_A = ‖v‖_{A⁻¹}`, p. 72, PDF p. 94, so `‖v‖*²_H = ‖v‖²_{H⁻¹}`,
using Mathlib's total operator inverse `H.inverse`). Positive-definiteness of `H` is stated as a
uniform (coercive) lower bound `∃ c > 0, ∀ w, c‖w‖² ≤ ⟪w, Hw⟫` rather than the pointwise
`∀ w ≠ 0, 0 < ⟪w, Hw⟫`: on an infinite-dimensional `E`, pointwise positive-definiteness alone does
not guarantee `H` is boundedly invertible (its spectrum can accumulate at `0`), in which case
`H.inverse` silently falls back to Mathlib's junk zero operator and `nsq` would no longer be the
true local dual norm. Coercivity forces `H` to be a genuine `ContinuousLinearEquiv`, so `H.inverse`
is the true inverse; every regularizer this chapter's theorems apply to (strongly convex, smooth,
twice differentiable on the sets §5.1 works with) satisfies a uniform Hessian lower bound, so no
book-admissible instance is excluded by requiring it explicitly. -/
def IsLocalDualNormSq (R : E → ℝ) (gradR : E → E) (x y v : E) (nsq : ℝ) : Prop :=
  ∃ (a : ℝ) (H : E →L[ℝ] E),
    a ∈ Set.Icc (0 : ℝ) 1 ∧
    HasFDerivAt gradR H (a • x + (1 - a) • y) ∧
    IsSelfAdjoint H ∧
    (∃ c : ℝ, 0 < c ∧ ∀ w : E, c * ‖w‖ ^ 2 ≤ quadForm H w) ∧
    BregmanDivergence R gradR x y = (1 / 2) * quadForm H (x - y) ∧
    nsq = quadForm H.inverse v

/-- `D_R²`, the squared diameter of `K` relative to the regularizer `R` (book p. 72, PDF p. 94):
`D_R² = max_{x,y ∈ K} (R(x) - R(y))`, rendered as a supremum over `K × K`. -/
noncomputable def RDiameterSq (R : E → ℝ) (K : Set E) : ℝ :=
  ⨆ x ∈ K, ⨆ y ∈ K, (R x - R y)

/-- The auxiliary functions `g_t` used in the proof of Lemma 5.3/5.4 (book p. 75, PDF p. 97):
`g_0(x) = (1/η) R(x)` and, for `n ≥ 1`, `g_n(x) = ∇_n^⊤ x` where `∇_n` is the book's gradient at
round `n` — here `grad (n - 1)`, since `grad t` denotes the gradient of `f t` at `x t` in this
chapter's 0-indexed convention (round `t`, `t ∈ ℕ`, is the book's round `t + 1`). -/
noncomputable def gFun (η : ℝ) (R : E → ℝ) (grad : ℕ → E) : ℕ → E → ℝ
  | 0, x => (1 / η) * R x
  | n + 1, x => ⟪grad n, x⟫_ℝ

/-- `(x, grad)` is a run of the RFTL algorithm (Algorithm 13, book p. 74, PDF p. 96) on cost
functions `f` over decision set `K`, with regularizer `R` (gradient map `gradR`) and step size
`η > 0`: the initial decision `x 0` minimizes `R` over `K` (the book's `x_1`); at every round
`t`, `grad t` is the gradient of `f t` at `x t` (`∇_t := ∇f_t(x_t)`, `t` here is the book's
`t + 1`); and the next decision `x (t + 1)` minimizes, over `K`, `y ↦ η * Σ_{s ≤ t} ⟪grad s, y⟫
+ R y` — the book's `x_{t+2} = arg min_{x ∈ K} {η Σ_{s=1}^{t+1} ∇_s^⊤ x + R(x)}` under the same
shift. -/
def IsRFTLRun (K : Set E) (R : E → ℝ) (η : ℝ) (f : ℕ → E → ℝ) (x grad : ℕ → E) : Prop :=
  IsArgMinOn R K (x 0) ∧
  (∀ t : ℕ, HasGradientAt (f t) (grad t) (x t)) ∧
  ∀ t : ℕ, IsArgMinOn (fun y => η * (∑ s ∈ Finset.range (t + 1), ⟪grad s, y⟫_ℝ) + R y) K (x (t + 1))

/-- `(x, grad, y)` is a run of the agile Online Mirror Descent algorithm (Algorithm 14, agile
version, book p. 78, PDF p. 100) on cost functions `f` over decision set `K`, with regularizer
`R` (gradient map `gradR`) and step size `η > 0`: `gradR (y 0) = 0` and `x 0` minimizes over `K`
the Bregman divergence to `y 0` (the book's `∇R(y_1) = 0`, `x_1 = arg min_{x∈K} B_R(x‖y_1)`); at
every round `t`, `grad t` is the gradient of `f t` at `x t`; the dual point updates by
`∇R(y_{t+1}) = ∇R(x_t) - η grad_t` (the book's agile rule `∇R(y_{t+1}) = ∇R(x_t) - η∇_t`); and
`x (t + 1)` minimizes over `K` the Bregman divergence to `y (t + 1)` (the book's projection
`x_{t+1} = arg min_{x∈K} B_R(x‖y_{t+1})`). Indices follow the same 0-indexed shift as
`IsRFTLRun`. -/
def IsOMDAgileRun (K : Set E) (R : E → ℝ) (gradR : E → E) (η : ℝ)
    (f : ℕ → E → ℝ) (x grad y : ℕ → E) : Prop :=
  gradR (y 0) = 0 ∧
  IsArgMinOn (fun z => BregmanDivergence R gradR z (y 0)) K (x 0) ∧
  (∀ t : ℕ, HasGradientAt (f t) (grad t) (x t)) ∧
  (∀ t : ℕ, gradR (y (t + 1)) = gradR (x t) - η • grad t) ∧
  (∀ t : ℕ, IsArgMinOn (fun z => BregmanDivergence R gradR z (y (t + 1))) K (x (t + 1)))

end OnlineConvexOpt.Regularization


