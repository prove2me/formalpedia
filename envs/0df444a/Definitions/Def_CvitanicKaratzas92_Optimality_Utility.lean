-- Prove2me | Definitions.Def_CvitanicKaratzas92_Optimality_Utility
-- name    : CvitanicKaratzas92_Optimality_Utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:51:09.464022+00:00
-- url     : https://prove2.me/theorems/62e756ca-f7cd-4082-9bee-bea4c6578227
-- title:
--   Sections 4–5 — the support function $\delta(\cdot\mid K)$, the barrier cone $\tilde K$, utility functions, $I$, $\tilde U$ and conditions (5.8), (8.25)
-- statement:
--   **Constraint set** (Section 4). $K\subset\mathbb R^d$ is a nonempty, closed, convex set, and
--   $$\delta(x)\equiv\delta(x\mid K)=\sup_{\pi\in K}(-\pi^*x)\ \in\ \mathbb R\cup\{+\infty\} \tag{4.1}$$
--   is the support function of $-K$; its effective domain is the barrier cone $\tilde K=\{x\in\mathbb R^d;\ \delta(x\mid K)<\infty\}$ (4.2). The paper assumes throughout that (4.3) $\delta(\cdot\mid K)$ is continuous on $\tilde K$, and (4.4) $\delta(x\mid K)\ge\delta_0$ for all $x\in\mathbb R^d$, for some $\delta_0\in\mathbb R$.
--
--   **Utility functions** (Section 5). A function $U:(0,\infty)\to\mathbb R$ is a *utility function* if it is strictly increasing, strictly concave, of class $C^1$ and satisfies
--   $$U'(0+)=\lim_{x\downarrow0}U'(x)=\infty,\qquad U'(\infty)=\lim_{x\to\infty}U'(x)=0. \tag{5.1}$$
--   $I$ denotes the inverse of $U'$, which maps $(0,\infty)$ onto itself, and
--   $$\tilde U(y)=\max_{x>0}\,[\,U(x)-xy\,],\qquad 0<y<\infty, \tag{5.2}$$
--   is the Legendre–Fenchel transform. Two optional conditions appear later: (5.8) $c\mapsto cU'(c)$ is nondecreasing on $(0,\infty)$; and (8.25): $U_2$ and every $U_1(t,\cdot)$, $t\in[0,T]$, satisfy (5.9) with the same constants, i.e. there are $\alpha\in(0,1)$, $\gamma\in(1,\infty)$ with $\alpha U'(x)\ge U'(\gamma x)$ for all $x\in(0,\infty)$.
--
--   **The pair of utilities** (Section 6). $U_1:[0,T]\times(0,\infty)\to\mathbb R$ is continuous and every $U_1(t,\cdot)$ is a utility function (with $U_1'$, $I_1$, $\tilde U_1$ taken in the second variable); $U_2$ is a utility function.
--
--   **Formalization Note** $\delta$ is computed in the extended reals, so $\delta(x)=+\infty$ off $\tilde K$; (4.3) is continuity of the real-valued restriction to $\tilde K$. A utility function is a function $\mathbb R\to\mathbb R$ whose values off $(0,\infty)$ play no role; $U'$ is the derivative. $I(y)$ is defined as $\inf\{x>0:\ U'(x)\le y\}$, which for $y>0$ is the unique $x>0$ with $U'(x)=y$. $\tilde U(y)$ is the supremum of $\{U(x)-xy:\ x>0\}$, finite for $y>0$ (and attained at $x=I(y)$, so it is the paper's maximum). Both $I$ and $\tilde U$ are only meaningful for $y>0$, the domain the paper gives them; for $y\le0$ the Lean definitions return the default value $0$, and every statement of the series evaluates them at positive arguments only. At a zero argument (zero consumption, zero terminal wealth) the paper uses $U(0+)\in[-\infty,\infty)$; the definition `uExt` returns $U(x)$ for $x>0$ and $U(0+)=\inf_{z>0}U(z)$ otherwise.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 771–773, Section 4 (4.1)–(4.4), Section 5 (5.1)–(5.2), (5.8)–(5.9), Section 6; p. 779, (8.25)

import Mathlib

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CvitanicKaratzas92.Optimality

variable {d : ℕ}

/-- (4.1), p. 771: the support function of `−K`,
`δ(x) = δ(x | K) = sup_{π ∈ K} (−π*x)`, with values in `ℝ ∪ {+∞}` (computed in `EReal`). -/
noncomputable def delta (K : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    EReal :=
  ⨆ p ∈ K, ((-inner ℝ p x : ℝ) : EReal)

/-- (4.2), p. 771: the barrier cone `K̃ = {x ∈ ℝᵈ ; δ(x | K) < ∞}` of `−K`. -/
def barrierCone (K : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | delta K x < ⊤}

/-- Standing assumptions of Section 4 (p. 771) on the constraint set: `K` is nonempty, closed and
convex; (4.3) `δ(· | K)` is continuous on `K̃`; (4.4) `δ(x | K) ≥ δ₀` for all `x`, some real
`δ₀`. -/
def IsConstraintSet (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧
  ContinuousOn (fun x => (delta K x).toReal) (barrierCone K) ∧
  ∃ δ₀ : ℝ, ∀ x, (δ₀ : EReal) ≤ delta K x

/-- Section 5, p. 772: `U : (0, ∞) → ℝ` is a utility function — strictly increasing, strictly
concave, of class `C¹` on `(0, ∞)`, with (5.1) `U'(0+) = ∞` and `U'(∞) = 0`. Values of `U` off
`(0, ∞)` play no role. -/
def IsUtility (U : ℝ → ℝ) : Prop :=
  StrictMonoOn U (Ioi 0) ∧ StrictConcaveOn ℝ (Ioi 0) U ∧ ContDiffOn ℝ 1 U (Ioi 0) ∧
  Tendsto (deriv U) (𝓝[>] 0) atTop ∧ Tendsto (deriv U) atTop (𝓝 0)

/-- Section 5, p. 772: `I`, the inverse of `U'`. For a utility function `U'` is a continuous
strictly decreasing bijection of `(0, ∞)` onto itself, so for `y > 0` this infimum is the
unique `x > 0` with `U'(x) = y`. -/
noncomputable def invMarginal (U : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {x | 0 < x ∧ deriv U x ≤ y}

/-- (5.2), p. 772: the Legendre–Fenchel transform `Ũ(y) = max_{x > 0} [U(x) − xy]`, `y > 0`
(a supremum of the image of `(0, ∞)`, finite for `y > 0` when `U` is a utility function). -/
noncomputable def conj (U : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup ((fun x => U x - x * y) '' Ioi 0)

/-- `U` extended to `[0, ∞)` with values in `[−∞, ∞)`: `U(x)` for `x > 0` and
`U(0+) = inf_{z > 0} U(z)` otherwise (the paper's value of a utility at zero consumption or
zero terminal wealth). -/
noncomputable def uExt (U : ℝ → ℝ) (x : ℝ) : EReal :=
  if 0 < x then (U x : EReal) else ⨅ z ∈ Ioi (0 : ℝ), (U z : EReal)

/-- (5.8), p. 772: `c ↦ cU'(c)` is nondecreasing on `(0, ∞)`. -/
def Cond58 (U : ℝ → ℝ) : Prop :=
  MonotoneOn (fun c => c * deriv U c) (Ioi 0)

/-- (8.25), p. 779 (with (5.9), p. 772): `U₂` and every `U₁(t, ·)`, `t ∈ [0, T]`, satisfy (5.9)
with the same constants: there are `α ∈ (0, 1)`, `γ ∈ (1, ∞)` such that `αU'(x) ≥ U'(γx)` for
all `x > 0`. -/
def Cond825 (T : ℝ≥0) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) : Prop :=
  ∃ α ∈ Ioo (0 : ℝ) 1, ∃ γ ∈ Ioi (1 : ℝ),
    (∀ x > 0, deriv U2 (γ * x) ≤ α * deriv U2 x) ∧
    ∀ t ≤ T, ∀ x > 0, deriv (U1 t) (γ * x) ≤ α * deriv (U1 t) x

/-- Section 6, p. 773: `U₁ : [0, T] × (0, ∞) → ℝ` is continuous and every `U₁(t, ·)` is a
utility function; `U₂` is a utility function. -/
def IsUtilityPair (T : ℝ≥0) (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ≥0 × ℝ => U1 p.1 p.2) {p | p.1 ≤ T ∧ 0 < p.2} ∧
  (∀ t ≤ T, IsUtility (U1 t)) ∧ IsUtility U2

end CvitanicKaratzas92.Optimality


