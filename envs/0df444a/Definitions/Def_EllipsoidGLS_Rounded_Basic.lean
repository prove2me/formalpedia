-- Prove2me | Definitions.Def_EllipsoidGLS_Rounded_Basic
-- name    : EllipsoidGLS_Rounded_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:46:14.413881+00:00
-- url     : https://prove2.me/theorems/6eae489c-46b1-480a-9747-fe3ee7389fa2
-- title:
--   §1 (5)–(7) and §2, pp. 172–173 — Euclidean norm, δ-neighbourhood S(K, δ), convex body (K, n, a₀, r, R), volume of the unit ball
-- statement:
--   Basic objects of Grötschel, Lovász and Schrijver's treatment of the ellipsoid method on convex bodies. Throughout, $\mathbb{R}^n$ carries the **Euclidean** norm.
--
--   1. **Euclidean norm.** For $v\in\mathbb{R}^n$, $\|v\| = \sqrt{v^{\mathsf T}v}$.
--   2. **$\delta$-neighbourhood.** For $K\subseteq\mathbb{R}^n$ and $\delta\in\mathbb{R}$,
--   $$S(K,\delta) = \{\,y\in\mathbb{R}^n : \|y-x\|\le\delta \text{ for some } x\in K\,\}.$$
--   For a compact $K$ this is the set of points at Euclidean distance $d(y,K)\le\delta$ from $K$, the set appearing in the weak separation problem.
--   3. **Convex body.** Given $K\subseteq\mathbb{R}^n$, a point $a_0\in\mathbb{R}^n$ and reals $r,R$, the tuple $(K,a_0,r,R)$ is a (compact) convex body if $K$ is convex and compact, $0<r\le R$, and
--   $$S(a_0,r)\subseteq K\subseteq S(a_0,R),$$
--   where $S(a_0,\rho)=\{x:\|x-a_0\|\le\rho\}$ is the closed Euclidean ball, written as the ellipsoid $E(a_0,\rho^2 I)$.
--   4. **Volume of the unit ball.** $V_m$ is the $m$-dimensional Lebesgue volume of the Euclidean unit ball of $\mathbb{R}^m$.
--
--   These objects fix the setting of every statement of the mission: the body $K$ is known only through a weak separation oracle, and the two balls of radii $r$ and $R$ are the a priori information that makes the ellipsoid method's step count finite.
--
--   **Formalization Note** $\mathbb{R}^n$ is `Fin n → ℝ`, on which Mathlib's `‖·‖` is the sup norm, so the Euclidean norm is written out as `euclNorm`. The paper's convex body also requires $n\ge 2$; that condition is a separate hypothesis of each theorem. The paper's definition (p. 172) asks for a convex set with $a_0\in K$; §2 (p. 173) works with compact convex sets, and compactness is included here ($a_0\in K$ follows from $S(a_0,r)\subseteq K$). The balls use the published `LinearOptimization.ellipsoidBall`, which equals the Euclidean ball for a positive radius.
-- source:
--   Grötschel, Lovász, Schrijver, The ellipsoid method and its consequences in combinatorial optimization, Combinatorica 1 (1981), pp. 172–173, §1 (5)–(7), §2; p. 176, V_n after (32)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid

namespace EllipsoidGLS.Rounded

open Matrix

/-- The Euclidean norm `‖v‖ = √(vᵀv)` on `ℝⁿ = Fin n → ℝ` (p. 173). Mathlib's `‖·‖` on
`Fin n → ℝ` is the sup norm, so the paper's norm is written out. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- The closed `δ`-neighbourhood `S(K, δ) = {y | d(y, K) ≤ δ}` of `K` in the Euclidean
distance (§1 (6), p. 172, and §2, p. 173): the points within Euclidean distance `δ` of some
point of `K` (for compact `K` the distance is attained). -/
def nbhd {n : ℕ} (K : Set (Fin n → ℝ)) (δ : ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ x ∈ K, euclNorm (y - x) ≤ δ}

/-- `(K, n, a₀, r, R)` is a compact convex body (§1, p. 172, (7), and §2, p. 173):
`K ⊆ ℝⁿ` is compact and convex, `0 < r ≤ R`, and `S(a₀, r) ⊆ K ⊆ S(a₀, R)` for the
Euclidean balls `S(a₀, ρ) = E(a₀, ρ²I)`. The paper's `n ≥ 2` is a separate hypothesis
of each theorem. -/
def IsConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) (a₀ : Fin n → ℝ) (r R : ℝ) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ 0 < r ∧ r ≤ R ∧
    LinearOptimization.ellipsoidBall a₀ r ⊆ K ∧ K ⊆ LinearOptimization.ellipsoidBall a₀ R

/-- `V_m`, the `m`-dimensional volume (Lebesgue measure) of the Euclidean unit ball of
`ℝᵐ` (p. 176, after (32)). -/
noncomputable def unitBallVol (m : ℕ) : ℝ :=
  (MeasureTheory.volume (LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1)).toReal

end EllipsoidGLS.Rounded


