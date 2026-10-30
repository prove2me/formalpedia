-- Prove2me | Definitions.Def_NonStrongConvexGM_QuasiStrong_Model
-- name    : NonStrongConvexGM_QuasiStrong_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:39.676749+00:00
-- url     : https://prove2.me/theorems/226e0677-e2c5-4310-91ec-387dc2192524
-- title:
--   Smooth convex problems, relaxed classes and exact projected gradient
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex. A problem consists of a convex objective $f:X\to\mathbb R$, an attained minimum, a supplied gradient field $g$, and $L>0$, satisfying
--
--   $$Df(x)[v]=\langle g(x),v\rangle\ \text{within }X,\qquad \|g(x)-g(y)\|\le L\|x-y\|\quad(x,y\in X).$$
--
--   The argmin $X^*=\{x\in X:\forall y\in X,\ f(x)\le f(y)\}$, Euclidean space and nearest-point predicate are reused from the published setting. The value $f^*$ is $f$ at an actual minimizer; $[u]_C$ selects an actual nearest point of $C$, and $\bar x=[x]_{X^*}$. For $\kappa>0$, define the independent classes by
--
--   $$\begin{aligned}
--   S:&\ f(y)\ge f(x)+\langle g(x),y-x\rangle+\tfrac\kappa2\|x-y\|^2 &&(x,y\in X),\\
--   qS:&\ f^*\ge f(x)+\langle g(x),\bar x-x\rangle+\tfrac\kappa2\|x-\bar x\|^2 &&(x\in X),\\
--   G:&\ \langle g(x)-g(\bar x),x-\bar x\rangle\ge\kappa\|x-\bar x\|^2 &&(x\in X),\\
--   U:&\ f(x)\ge f^*+\langle g(\bar x),x-\bar x\rangle+\tfrac\kappa2\|x-\bar x\|^2 &&(x\in X),\\
--   F:&\ f(x)-f^*\ge\tfrac\kappa2\|x-\bar x\|^2 &&(x\in X).
--   \end{aligned}$$
--
--   The model also names the original Jensen strong-convexity condition (5) and the gradient-monotonicity condition (7b). The exact constant-step projected gradient orbit and signed ratio are
--
--   $$x^0=x_0,\quad x^{k+1}=[x^k-L^{-1}g(x^k)]_X,\quad q=\frac{1-\kappa/L}{1+\kappa/L}.$$
--
--   This supplies the shared interface for the class inclusions and complete convergence target; none of these definitions assumes a conclusion of another class or convergence theorem.
--
--   **Formalization Note** The model intentionally generalizes the classical ambient-gradient reading to a derivative within $X$ represented by $g$, with arbitrary off-domain values. On-domain differentiability gives continuity; closed $X$ then gives a closed epigraph and closed actual optimizer set. The projection's zero branch only totalizes sets with no nearest point and is unreachable for the nonempty closed convex sets used here. The value has no default branch because attainment is required. Natural dimension includes zero. The GM first update is at $k=0$, the reading required by (45) and its proof. No bound $\kappa\le L$ is imposed.
-- source:
--   Necoara, Nesterov & Glineur, arXiv:1504.06298v4 (9 August 2016), https://arxiv.org/abs/1504.06298v4, §2, p. 3 (PDF p. 3), (1), (5); p. 4 (PDF p. 4), (7); Definitions 1–4, pp. 5, 7–8 (PDF pp. 5, 7–8), (10), (13), (17), (22); §5.1, p. 19 (PDF p. 19), GM and (45).

import Definitions.Def_NecoaraNG_Chain_Setting

namespace NonStrongConvexGM.QuasiStrong

/-- Section 2, p. 3: a convex smooth problem on a closed convex feasible set.
The supplied gradient represents differentiation within X; nothing is assumed off X.
ConvexOn includes convexity of X. Attainment is for the actual optimizer set.
Continuity within X and closed X imply closed epigraph and closed optimizer set. -/
structure Problem (n : ℕ) where
  X : Set (NecoaraNG.Chain.E n)
  f : NecoaraNG.Chain.E n → ℝ
  grad : NecoaraNG.Chain.E n → NecoaraNG.Chain.E n
  L : ℝ
  closed : IsClosed X
  convex : ConvexOn ℝ X f
  derivative : ∀ x ∈ X, HasFDerivWithinAt f (innerSL ℝ (grad x)) X x
  L_pos : 0 < L
  grad_lipschitz : ∀ x ∈ X, ∀ y ∈ X, ‖grad x - grad y‖ ≤ L * ‖x - y‖
  attained : (NecoaraNG.Chain.optSet X f).Nonempty

/-- The minimum is evaluated at an actual optimizer, whose existence is part of Problem. -/
noncomputable def value {n : ℕ} (P : Problem n) : ℝ := P.f (Classical.choose P.attained)

/-- Exact nearest-point selection. The zero branch totalizes invalid sets only.
For the nonempty closed convex feasible/optimal sets of Problem a nearest point exists
and is unique, so this branch is never used by the theorem. -/
noncomputable def project {n : ℕ} (C : Set (NecoaraNG.Chain.E n))
    (u : NecoaraNG.Chain.E n) : NecoaraNG.Chain.E n := by
  classical
  exact if h : ∃ p, NecoaraNG.Chain.IsNearest C u p then Classical.choose h else 0

/-- The actual nearest optimizer, using the published argmin definition. -/
noncomputable def nearestOpt {n : ℕ} (P : Problem n) (x : NecoaraNG.Chain.E n) :=
  project (NecoaraNG.Chain.optSet P.X P.f) x

/-- First-order strong convexity, first condition in (7), p. 4. -/
def Strong {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X, ∀ y ∈ P.X,
    P.f x + inner ℝ (P.grad x) (y - x) + κ / 2 * ‖x - y‖ ^ 2 ≤ P.f y

/-- The original strong-convexity definition (5), p. 3. -/
def StrongJensen {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X, ∀ y ∈ P.X, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
    P.f (a • x + (1 - a) • y) ≤
      a * P.f x + (1 - a) * P.f y - κ * a * (1 - a) / 2 * ‖x - y‖ ^ 2

/-- Second equivalent condition in (7), p. 4. -/
def StrongMonotone {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X, ∀ y ∈ P.X,
    κ * ‖x - y‖ ^ 2 ≤ inner ℝ (P.grad x - P.grad y) (x - y)

/-- Definition 1, (10), p. 5; common convex smooth assumptions live in Problem. -/
def IsQuasiStrong {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X,
    P.f x + inner ℝ (P.grad x) (nearestOpt P x - x) +
      κ / 2 * ‖x - nearestOpt P x‖ ^ 2 ≤ value P

/-- Definition 2, (13), p. 5: retain the gradient term at the constrained optimizer. -/
def UnderApprox {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X,
    value P + inner ℝ (P.grad (nearestOpt P x)) (x - nearestOpt P x) +
      κ / 2 * ‖x - nearestOpt P x‖ ^ 2 ≤ P.f x

/-- Definition 3, (17), p. 7. -/
def GradientGrowth {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X,
    κ * ‖x - nearestOpt P x‖ ^ 2 ≤
      inner ℝ (P.grad x - P.grad (nearestOpt P x)) (x - nearestOpt P x)

/-- Definition 4, (22), p. 8; no other class or convergence certificate is assumed. -/
def FunctionalGrowth {n : ℕ} (P : Problem n) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ P.X, κ / 2 * ‖x - nearestOpt P x‖ ^ 2 ≤ P.f x - value P

/-- GM, p. 19, with step 1/L. The first update is at k=0, as required by (45)
and the proof on pp. 20–21, despite the box's printed k≥1. -/
noncomputable def orbit {n : ℕ} (P : Problem n) (x₀ : NecoaraNG.Chain.E n) :
    ℕ → NecoaraNG.Chain.E n
  | 0 => x₀
  | k + 1 => project P.X (orbit P x₀ k - (1 / P.L) • P.grad (orbit P x₀ k))

/-- Signed ratio from (45). No κ≤L restriction or clamping in all-optimal instances. -/
noncomputable def rate {n : ℕ} (P : Problem n) (κ : ℝ) : ℝ :=
  (1 - κ / P.L) / (1 + κ / P.L)

end NonStrongConvexGM.QuasiStrong


