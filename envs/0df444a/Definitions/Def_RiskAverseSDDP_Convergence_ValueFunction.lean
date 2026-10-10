-- Prove2me | Definitions.Def_RiskAverseSDDP_Convergence_ValueFunction
-- name    : RiskAverseSDDP_Convergence_ValueFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:44:50.012135+00:00
-- url     : https://prove2.me/theorems/3f7d1340-4c33-45cc-9c94-ca020cdd0835
-- title:
--   (2.1)–(2.2), Assumption (H), p. 3 — the value function of a convex program and its assumptions
-- statement:
--   Let $X\subseteq\mathbb R^m$ and $Y\subseteq\mathbb R^n$, let $f:\mathbb R^m\times\mathbb R^n\to\mathbb R\cup\{+\infty\}$, let $g=(g_1,\dots,g_p):\mathbb R^m\times\mathbb R^n\to(\mathbb R\cup\{+\infty\})^p$, and let $A$, $B$ be matrices and $b$ a vector of compatible sizes. The **value function** of (2.1) is
--   $$
--   \mathcal Q(x)=\inf\{f(x,y):\ y\in S(x)\},\qquad S(x)=\{y\in Y:\ Ax+By=b,\ g(x,y)\le0\},
--   $$
--   with the convention $\inf\emptyset=+\infty$; it is defined for every $x\in\mathbb R^m$.
--
--   For $\varepsilon>0$ the **$\varepsilon$-fattening** of $X$ is $X^\varepsilon=X+\varepsilon\mathbb B_m$ (2.2), where $\mathbb B_m$ is the closed Euclidean unit ball. **Assumption (H)** for a given $\varepsilon$ consists of: $X$ and $Y$ are nonempty, compact and convex (as stated with (2.1)); 1) $f$ is lower semicontinuous, proper and convex; 2) each component $g_i$ is convex and lower semicontinuous; 3) $\varepsilon>0$ and $X^\varepsilon\times Y\subseteq\operatorname{dom}f$.
--
--   These objects are the setting of Proposition 2.2, which bounds subgradients of $\mathcal Q$.
--
--   **Formalization Note** Values in $\mathbb R\cup\{\pm\infty\}$ are `EReal`, and the infimum is an `EReal` infimum. The fattening is written as the closed thickening $\{x:\operatorname{dist}(x,X)\le\varepsilon\}$, which equals $X+\varepsilon\mathbb B_m$ for compact $X$. $A$ and $B$ are linear maps. Convexity of an extended-real function is convexity of its epigraph.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 3, (2.1), (2.2), Assumption (H)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic

namespace RiskAverseSDDP.Convergence

/-- The data of the convex program (2.1), p. 3, with `x ∈ ℝᵐ`, `y ∈ ℝⁿ`, `q` linear equality
constraints and `p` nonlinear constraints:
* `X ⊆ ℝᵐ`, `Y ⊆ ℝⁿ` the sets of (2.1);
* `f : ℝᵐ × ℝⁿ → ℝ ∪ {+∞}` the objective;
* `g : ℝᵐ × ℝⁿ → (ℝ ∪ {+∞})ᵖ` the constraint function, read componentwise;
* the matrices `A`, `B` (as linear maps) and the right-hand side `b` of `Ax + By = b`. -/
structure VFData (m n q p : ℕ) where
  X : Set (EuclideanSpace ℝ (Fin m))
  Y : Set (EuclideanSpace ℝ (Fin n))
  f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → EReal
  g : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → Fin p → EReal
  A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin q)
  B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin q)
  b : EuclideanSpace ℝ (Fin q)

namespace VFData

variable {m n q p : ℕ} (D : VFData m n q p)

/-- The feasible set of (2.1): `S(x) = {y ∈ Y : Ax + By = b, g(x, y) ≤ 0}`. -/
def S (x : EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | y ∈ D.Y ∧ D.A x + D.B y = D.b ∧ ∀ i, D.g (x, y) i ≤ 0}

/-- The value function (2.1): `𝒬(x) = inf {f(x, y) : y ∈ S(x)}`, an infimum in `ℝ ∪ {±∞}`
(`+∞` when `S(x) = ∅`), defined for every `x ∈ ℝᵐ`. -/
noncomputable def Q (x : EuclideanSpace ℝ (Fin m)) : EReal :=
  ⨅ y ∈ D.S x, D.f (x, y)

/-- Assumption (H), p. 3, with the standing assumptions on `X` and `Y` stated with (2.1):
`X` and `Y` are nonempty, compact and convex;
1) `f` is lower semicontinuous, proper and convex;
2) every component `g_i` of `g` is a convex lower semicontinuous function;
3) `ε > 0` and `X^ε × Y ⊆ dom f`, where `X^ε = X + ε𝔹_m` (2.2). -/
def H (ε : ℝ) : Prop :=
  D.X.Nonempty ∧ IsCompact D.X ∧ Convex ℝ D.X ∧
  D.Y.Nonempty ∧ IsCompact D.Y ∧ Convex ℝ D.Y ∧
  (LowerSemicontinuous D.f ∧ EProper D.f ∧ EConvex D.f) ∧
  (∀ i, EConvex (fun z => D.g z i) ∧ LowerSemicontinuous (fun z => D.g z i)) ∧
  (0 < ε ∧ ∀ x ∈ Metric.cthickening ε D.X, ∀ y ∈ D.Y, D.f (x, y) < ⊤)

end VFData

end RiskAverseSDDP.Convergence


