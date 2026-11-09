-- Prove2me | Definitions.Def_MulticalibrationGGM_Reduction_Model
-- name    : MulticalibrationGGM_Reduction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:18.622917+00:00
-- url     : https://prove2.me/theorems/76ee4f37-174a-4171-9fbd-67f5d45a1ca7
-- title:
--   Signed test payoffs and expected variational inequalities
-- statement:
--   Let $X$ be an arbitrary feature space, $d$ a finite dimension, and $Y\subseteq\mathbb R^d$ the full set of possible forecasts and outcomes. A test is any function $h:X\times Y\to\mathbb R^d$. A class $H$ is a class of bounded tests when each member has its own finite bound on $\|h(x,p)\|$, uniformly in $(x,p)$. No common bound, finiteness, symmetry, continuity, or measurability of all tests is imposed.
--
--   For $x\in X$, an outcome $y\in Y$, and a probability law $D$ on $Y$, the signed expected payoff is
--
--   $$\mathbb E_{p\sim D}[h(x,p)^\top(y-p)].$$
--
--   A law $D$ solves the expected variational inequality for a vector field $g:Y\to\mathbb R^d$ to tolerance $\varepsilon\ge0$ when
--
--   $$\mathbb E_{p\sim D}[g(p)^\top(y-p)]\le\varepsilon\qquad\text{for every }y\in Y.$$
--
--   This certificate is the oracle primitive used by Algorithm 1. It is uniform in the as yet unrevealed outcome; it contains no calibration or regret conclusion.
--
--   **Formalization Note** Coordinates are indexed by `Fin d`, tests are curried, and laws are Mathlib probability measures on the subtype $Y$ with its Borel structure. An EVI certificate includes integrability for each of its scalar payoffs. Other uses of the expected-payoff definition require the corresponding integrability in the validity condition of the algorithm module. This exposes the source's convention that its displayed expectations are well defined, without imposing global regularity on the tests.
-- source:
--   Gabriele Farina, Juan Perdomo, An Efficient Black-Box Reduction from Online Learning to Multicalibration, and a New Route to Φ-Regret Minimization, STOC 2027 submission #721 (October 2026), Definition 1, p. 5; §2.1 and Equation (1), p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf. PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

import Mathlib

open MeasureTheory
open scoped NNReal

namespace MulticalibrationGGM.Reduction

/-!
Farina and Perdomo, STOC 2027 submission #721 (October 2026), Definition 1,
p. 5; §2.1 and Equation (1), p. 11.
https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf
PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.
-/

/-- Coordinates for the paper's arbitrary finite-dimensional real outcome space. -/
abbrev Vector (d : ℕ) := Fin d → ℝ

/-- A test on the full prediction set, with no regularity condition. Currying changes
only the representation of the source's domain `X × Y`. -/
abbrev Test (X : Type*) {d : ℕ} (Y : Set (Vector d)) := X → Y → Vector d

/-- §2.1, p. 11: each test is bounded. The bound may depend on the test;
there is no uniform bound on the class and no finiteness or symmetry condition. -/
def BoundedTests {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    (H : Set (Test X Y)) : Prop :=
  ∀ h ∈ H, ∃ C : ℝ, 0 ≤ C ∧ ∀ x p, ‖h x p‖ ≤ C

/-- Definition 1, p. 5: signed test payoff `h(x,p)ᵀ(y-p)`. -/
def payoff {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    (h : Test X Y) (x : X) (y p : Y) : ℝ :=
  ∑ i : Fin d, h x p i * (y.val i - p.val i)

/-- Expected signed payoff under a normalized law on the full set `Y`.
All uses in the goal are guarded by `ValidRound`: Bochner integrability is required
under the actual law, without global measurability or continuity of the test. -/
noncomputable def expectedPayoff {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    (h : Test X Y) (x : X) (D : ProbabilityMeasure Y) (y : Y) : ℝ :=
  ∫ p, payoff h x y p ∂(D : Measure Y)

/-- Equation (1), p. 11: an approximate expected variational inequality for a
vector field `g` on `Y`. This is the general EVI object, independent of the learner
and the comparator class. Integrability expresses definedness of each expectation.
The certificate is uniform over all outcomes, including those chosen after `D`. -/
def SolvesEVI {d : ℕ} {Y : Set (Vector d)} (g : Y → Vector d)
    (D : ProbabilityMeasure Y) (ε : ℝ≥0) : Prop :=
  ∀ y : Y,
    Integrable (fun p : Y => ∑ i : Fin d, g p i * (y.val i - p.val i)) (D : Measure Y) ∧
    (∫ p : Y, (∑ i : Fin d, g p i * (y.val i - p.val i)) ∂(D : Measure Y)) ≤ (ε : ℝ)

end MulticalibrationGGM.Reduction


