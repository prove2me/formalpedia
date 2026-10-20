-- Prove2me | Definitions.Def_Gerver_monotone
-- name    : Gerver_monotone
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T19:29:51.826593+00:00
-- url     : https://prove2.me/theorems/3af5a40a-cc4d-45ed-9784-a36f93602640
-- title:
--   Strips, quarter-planes, caps, niches, and monotone sofas
-- statement:
--   The monotone-sofa structure of the moving sofa problem. Fix the unit vectors u_t = (cos t, sin t) and v_t = (-sin t, cos t). The parallelogram P_ω is the intersection of the horizontal strip ℝ × [0, 1] with the unit-width strip in the direction u_ω; the fan F_ω is the closed cone under it. A rotation path is a curve x of inner corners: for each t it determines a hallway with inner corner x(t), the image of the hallway under a rotation by t followed by a translation. Each such hallway splits as a closed outer quarter-plane Q_t⁺ at the outer corner x(t) + u_t + v_t minus an open inner quarter-plane Q_t⁻ at x(t). The cap K is the part of P_ω cut out by all outer quarter-planes over t ∈ [0, ω]; the niche is the part of the fan swept by the inner quarter-planes. The monotone sofa of the path is the common part of the strips and hallways over t ∈ [0, ω]; the path is supporting when it is continuous and both outer walls of each hallway touch the sofa. A polygon sofa is the intersection for a finite uniform angle set {iω/n : 1 ≤ i < n} of hallways translated by a corner map w; it is maximum when its area is maximal among such translations. A balanced maximum sofa is a moving sofa that is the Hausdorff limit (via Euclidean ε-neighborhoods) of maximum polygon sofas with angle sets Θ_{ω,n_i} over a strictly increasing sequence of powers of two. The rotation path X of angle π/2 satisfies the injectivity condition when it is continuously differentiable on [0, π/2] and its derivative points strictly against u_t and along v_t at every interior angle.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Definition 2.1.3, Definition 2.2.1, Equations (1.2)-(1.5), Definition 3.5.1, Definitions 3.5.2-3.5.3, Theorem 1.7.1 / Definition 6.1.2

import Mathlib
import Definitions.Def_Gerver_arena

namespace Gerver

/-- The unit vector u_t = (cos t, sin t) (Definition 2.1.3). -/
noncomputable def u (t : ℝ) : ℝ × ℝ := (Real.cos t, Real.sin t)

/-- The unit vector v_t = (-sin t, cos t) (Definition 2.1.3). -/
noncomputable def v (t : ℝ) : ℝ × ℝ := (-Real.sin t, Real.cos t)

/-- The dot product of two planar vectors. -/
def dot (a b : ℝ × ℝ) : ℝ := a.1 * b.1 + a.2 * b.2

/-- The horizontal strip H = ℝ × [0, 1] (Definition 1.2.3). -/
def stripH : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The vertical strip V rotated counterclockwise by ω: the unit-width strip
in the direction u_ω (Definition 1.2.3). -/
def stripV (ω : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ dot p (u ω) ∧ dot p (u ω) ≤ 1}

/-- The parallelogram P_ω = H ∩ V_ω (Section 1.2.2). -/
def para (ω : ℝ) : Set (ℝ × ℝ) := stripH ∩ stripV ω

/-- The fan F_ω: the closed cone bounded from below by the two bottom sides of
the parallelogram P_ω (Section 1.2.2). -/
def fan (ω : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ 0 ≤ dot p (u ω)}

/-- The hallway with inner corner x(t): the image of L under p ↦ x t + rot t p.
For x the inner-corner path of the supporting hallways of S, these are the
supporting hallways L_t of Equation (1.2) (Definition 2.2.2). -/
def hallAt (x : ℝ → ℝ × ℝ) (t : ℝ) : Set (ℝ × ℝ) :=
  (fun p => x t + rot t p) '' hallway

/-- The closed quarter-plane Q_t⁺ at the outer corner y(t) = x(t) + u_t + v_t
of the hallway with inner corner x(t): the closed quadrant bounded from above
by the two outer walls (Definition 2.2.1). -/
def Qplus (x : ℝ → ℝ × ℝ) (t : ℝ) : Set (ℝ × ℝ) :=
  {p | dot (p - (x t + u t + v t)) (u t) ≤ 0 ∧ dot (p - (x t + u t + v t)) (v t) ≤ 0}

/-- The open quarter-plane Q_t⁻ at the inner corner x(t): the open quadrant
bounded from above by the two inner walls (Definition 2.2.1), so that the
hallway with inner corner x(t) is Q_t⁺ \ Q_t⁻. -/
def Qminus (x : ℝ → ℝ × ℝ) (t : ℝ) : Set (ℝ × ℝ) :=
  {p | dot (p - x t) (u t) < 0 ∧ dot (p - x t) (v t) < 0}

/-- The cap K = C(S) of a rotation path: the part of the parallelogram P_ω cut
out by the closed quarter-planes at the outer corners (Equation (1.3)). -/
def capOf (x : ℝ → ℝ × ℝ) (ω : ℝ) : Set (ℝ × ℝ) :=
  para ω ∩ ⋂ t ∈ Set.Icc 0 ω, Qplus x t

/-- The niche N(K) of a rotation path: the part of the fan F_ω swept out by the
open quarter-planes at the inner corners (Equation (1.4)). -/
def nicheOf (x : ℝ → ℝ × ℝ) (ω : ℝ) : Set (ℝ × ℝ) :=
  fan ω ∩ ⋃ t ∈ Set.Icc 0 ω, Qminus x t

/-- The intersection I determined by a rotation path: the common part of the
two strips and the hallways with inner corners x(t), t ∈ [0, ω] (Equation
(1.2)). For x the supporting inner-corner path of a moving sofa S, this is the
monotone sofa containing S (Section 1.2.1). -/
def sofaOfPath (x : ℝ → ℝ × ℝ) (ω : ℝ) : Set (ℝ × ℝ) :=
  para ω ∩ ⋂ t ∈ Set.Icc 0 ω, (Qplus x t \ Qminus x t)

/-- A monotone sofa: an intersection of strips and hallways arising from some
rotation path x with angle ω ∈ (0, π/2] (Section 1.2.1). -/
def IsMonotoneSofa (S : Set (ℝ × ℝ)) : Prop :=
  ∃ (x : ℝ → ℝ × ℝ) (ω : ℝ), 0 < ω ∧ ω ≤ Real.pi / 2 ∧ S = sofaOfPath x ω

/-- The path x is a supporting rotation path of the monotone sofa
sofaOfPath x ω: x is continuous, and each hallway hallAt x t has both outer
walls touching the sofa — the supporting hallways of Definition 2.2.2, pushed
to contact with the sofa. The contact conditions pin down x as the canonical
inner-corner path of the sofa's supporting hallways. -/
def IsSupportingPathOf (x : ℝ → ℝ × ℝ) (ω : ℝ) : Prop :=
  Continuous x ∧ ∀ t ∈ Set.Icc 0 ω,
    (∃ p ∈ sofaOfPath x ω, dot (p - x t) (u t) = 1) ∧
    (∃ q ∈ sofaOfPath x ω, dot (q - x t) (v t) = 1)

/-- The uniform angle set Θ_{ω,n} = {iω/n : 1 ≤ i < n} of n intervals
(Definition 3.5.1). -/
def uniformAngles (ω : ℝ) (n : ℕ) : Set ℝ :=
  (fun i => (i : ℝ) * ω / (n : ℝ)) '' Set.Ico (1 : ℕ) n

/-- The polygon intersection S_Θ for the uniform angle set of n intervals: the
common part of the two strips and the hallways of angles iω/n, 1 ≤ i < n, the
hallway of angle t translated so that its inner corner is w(t) (Equation
(1.5)). -/
def polySofa (w : ℝ → ℝ × ℝ) (ω : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  para ω ∩ ⋂ t ∈ uniformAngles ω n, hallAt w t

/-- S is a maximum polygon sofa with uniform angle set Θ_{ω,n}: it has the
form polySofa w ω n and its area is maximal among all such polygon
intersections (Equation (1.5) with the maximization of Theorem 3.4.3). -/
def IsMaxPolygonSofa (S : Set (ℝ × ℝ)) (ω : ℝ) (n : ℕ) : Prop :=
  ∃ w, S = polySofa w ω n ∧ ∀ w', area (polySofa w' ω n) ≤ area S

/-- The Euclidean ε-neighborhood of a planar set: the points at squared
Euclidean distance less than ε² from some point of the set. -/
def nbhd (ε : ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  ⋃ p ∈ S, {q | dot (q - p) (q - p) < ε ^ 2}

/-- Convergence of sets in Hausdorff distance, phrased with Euclidean
ε-neighborhoods (Definition 3.5.2 (3)): for every ε > 0, from some index on the
sets F i lie in the ε-neighborhood of S and S lies in theirs. -/
def HausConv (F : ℕ → Set (ℝ × ℝ)) (S : Set (ℝ × ℝ)) : Prop :=
  ∀ ε > 0, ∃ N, ∀ i ≥ N, F i ⊆ nbhd ε S ∧ S ⊆ nbhd ε (F i)

/-- A balanced maximum sofa with rotation angle ω (Definition 3.5.2 and
Definition 3.5.3, stated at the level of sofas): a moving sofa that is the
Hausdorff limit of maximum polygon sofas whose uniform angle sets Θ_{ω,n_i}
run over a strictly increasing sequence of powers of two. -/
def IsBalancedMaximumSofa (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ∃ (F : ℕ → Set (ℝ × ℝ)) (n : ℕ → ℕ),
    (∀ i, ∃ k, n i = 2 ^ k) ∧
    (∀ i, 1 < n i) ∧
    (∀ i j, i < j → n i < n j) ∧
    (∀ i, IsMaxPolygonSofa (F i) ω (n i)) ∧
    HausConv F S ∧
    IsMovingSofa S

/-- The rotation path X of angle π/2 satisfies the injectivity condition
(Theorem 1.7.1 / Definition 6.1.2 (2)-(3)): X is continuously differentiable on
[0, π/2], and its derivative points strictly against u_t and along v_t for
every t ∈ (0, π/2) — the rotation path makes no self-loop. -/
def SatisfiesInjectivity (X : ℝ → ℝ × ℝ) : Prop :=
  ContDiffOn ℝ 1 X (Set.Icc 0 (Real.pi / 2)) ∧
  ∀ t ∈ Set.Ioo 0 (Real.pi / 2),
    dot (derivWithin X (Set.Icc 0 (Real.pi / 2)) t) (u t) < 0 ∧
    dot (derivWithin X (Set.Icc 0 (Real.pi / 2)) t) (v t) > 0

end Gerver


