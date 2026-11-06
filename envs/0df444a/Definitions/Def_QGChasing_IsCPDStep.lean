-- Prove2me | Definitions.Def_QGChasing_IsCPDStep
-- name    : QGChasing_IsCPDStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:11.375603+00:00
-- url     : https://prove2.me/theorems/5e81a14b-52f9-43c5-a07a-1c7585bc701f
-- title:
--   One round of Clipped Proximal Descent (Algorithm 1, lines 2–7)
-- statement:
--   Let $\kappa\ge1$, $X\subseteq\mathbb R^d$, a hitting cost $f$ and a previous decision $p=x_{t-1}$. A point $x$ is **the CPD decision $x_t$** if, for a global minimizer $v$ of $f$ (line 2) and $g=f-f(v)$, and for $v^X=\Pi_{\arg\min_{z\in X}g(z)}\,p$ (line 3), either
--
--   1. $g(v^X)\ge\beta\|v^X-p\|$ (line 4) and $x=v^X$ (line 5), or
--   2. $g(v^X)<\beta\|v^X-p\|$ and $x$ is the output of the balanced step of line 7, for some $(\mu,y)$.
--
--   This is Algorithm 1 for one round: move to the constrained minimizer nearest the previous decision when its hitting cost already pays for the movement, and otherwise take the balanced proximal step followed by the clipped correction.
--
--   **Formalization Note** The oracles are relations; a projection $\Pi_S w$ is a member of the published nearest-point set `SuperPolyak.nearestPoints S w`. For $f\in\mathcal F_\kappa$ the minimizer $v$ is unique, and the step exists and is unique.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Algorithm 1, lines 2–7, p.5; pp.5–6

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_IsCPDBalanced

namespace QGChasing

/-- One round of Clipped Proximal Descent, Algorithm 1, lines 2–7 (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.5; pp.5–6): from the
previous decision `p = x_{t−1}` and the revealed hitting cost `f = f_t`, the decision `x = x_t` is
produced as follows. Let `v` be the global minimizer of `f` (line 2) and `g(z) = f(z) − f(v)`; let
`v^X` be the point of `argmin_{z ∈ X} g(z)` nearest to `p` (line 3). If `g(v^X) ≥ β‖v^X − p‖`
(line 4) then `x = v^X` (line 5); otherwise `x` is the output of the balanced step (line 7,
`IsCPDBalanced`).

**Formalization Note** Every oracle is relational; `Π_S w` is a member of the published nearest-point
set `SuperPolyak.nearestPoints S w` (a closed convex nonempty `S` has exactly one). Line 2's `v_t` is "the global minimizer from
Assumption 3" (p.5), unique for costs in `F_κ`. The balanced branch carries the strict negation of
the line-4 test. -/
def IsCPDStep {d : ℕ} (κ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ) (p x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ v : EuclideanSpace ℝ (Fin d), (∀ z, f v ≤ f z) ∧
    ∃ vX : EuclideanSpace ℝ (Fin d), vX ∈ SuperPolyak.nearestPoints {z | z ∈ X ∧ ∀ w ∈ X, f z - f v ≤ f w - f v} p ∧
      ((cpdBeta κ * ‖vX - p‖ ≤ f vX - f v ∧ x = vX) ∨
        (f vX - f v < cpdBeta κ * ‖vX - p‖ ∧ ∃ (μ : ℝ) (y : EuclideanSpace ℝ (Fin d)), IsCPDBalanced κ X f p v μ y x))

end QGChasing


