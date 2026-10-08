-- Prove2me | Definitions.Def_OnlineConvexOpt_Regularization_Protocol_v2
-- name    : OnlineConvexOpt_Regularization_Protocol_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:17:02.015176+00:00
-- url     : https://prove2.me/theorems/3bde2fcb-49db-4eb1-ae8c-b0df69370d22
-- title:
--   RFTL/OMD protocol: argmin, Bregman divergence, local dual norm, $D_R^2$ (genuine supremum), RFTL and OMD runs
-- statement:
--   The Chapter 5 protocol definitions: minimizers over $K$, the squared operator norm, the Bregman divergence $B_R(x\|y)$, the local dual norm witness of Definition 5.1, the $R$-diameter $D_R^2=\sup\{R(x)-R(y):x,y\in K\}$, the auxiliary functions $g_t$, and the run predicates of RFTL (Algorithm 13) and agile OMD (Algorithm 14). Re-issued from `OnlineConvexOpt_Regularization_Protocol` with one change: $D_R^2$ (`RDiameterSq`) is the real supremum of the set $\{R(x)-R(y):x,y\in K\}$ instead of nested `⨆ x ∈ K, ⨆ y ∈ K` binders (junk-valued outside $K$); all other declarations are unchanged.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 72 (D_R, dual norms), p. 73, Definition 5.1 (Bregman divergence), p. 74, Algorithm 13 (RFTL), p. 78, Algorithm 14 (OMD) (PDF pp. 94–100)

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
`D_R² = max_{x,y ∈ K} (R(x) - R(y))`, rendered as the real supremum of the set
`{R x - R y | x, y ∈ K}` (`Set.image2`). It is the book's maximum whenever `K` is nonempty and
`R` is bounded on `K` (the book's standing situation: a continuous regularizer on a bounded
closed set); the retired version used nested `⨆ x ∈ K, ⨆ y ∈ K, …` binders, which on `ℝ`
evaluate to the junk value `sSup ∅ = 0` outside `K`. -/
noncomputable def RDiameterSq (R : E → ℝ) (K : Set E) : ℝ :=
  sSup (Set.image2 (fun p q => R p - R q) K K)

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


