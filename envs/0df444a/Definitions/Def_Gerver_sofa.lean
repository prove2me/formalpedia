-- Prove2me | Definitions.Def_Gerver_sofa
-- name    : Gerver_sofa
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T19:30:31.60237+00:00
-- url     : https://prove2.me/theorems/f672924e-938b-4d4e-bdc7-fe94799a3296
-- title:
--   The Gerver sofa structure and Mamikon's swept region
-- statement:
--   The structural characterization of Gerver's sofa and the swept-region arena. A Gerver sofa is a moving sofa equal to the monotone sofa of a continuously differentiable rotation path X on [0, π/2], together with angles 0 < φ < θ < π/4 and five curves A, C on [0, π/2], B on [π/2 - θ, π/2], D on [0, θ]: the contact points A(t), C(t) lie on the two outer walls of the hallway with inner corner X(t), B(t), D(t) on the two inner walls, and the curves satisfy Gerver's nine balancing ODEs on the five intervals cut by the angles, with B and D running along their wall directions. These are the structural properties the paper establishes for Gerver's sofa; the explicit curve formulas are Gerver's, solved from these ODEs. The Mamikon region of a base curve z, a length function α, and an interval [a, b] is the region swept by the segments from z(t) to z(t) + α(t)·v_t.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Definition 8.4.1, Theorems 8.4.1-8.4.2, Definition 7.4.1

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone

namespace Gerver

/-- Scalar multiplication of a planar vector by a real number. -/
def scale (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c * p.1, c * p.2)

/-- The region swept out by a family of tangent segments: the union over
t ∈ [a, b] of the segments from z(t) to z(t) + α(t) • v_t (Definition 7.4.1,
the Mamikon region). -/
def swept (z : ℝ → ℝ × ℝ) (α : ℝ → ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  ⋃ t ∈ Set.Icc a b, {p | ∃ s ∈ Set.Icc 0 1, p = z t + scale (s * α t) (v t)}

/-- A Gerver sofa: a moving sofa G equal to the monotone sofa sofaOfPath X (π/2)
determined by its rotation path X, whose supporting-hallway structure is
carried by the five curves of Definition 8.4.3 — A and C on [0, π/2], B on
[π/2 - θ, π/2], D on [0, θ] — with contact points A(t), C(t) on the outer walls,
B(t), D(t) on the inner walls, satisfying the balancing ODEs of Theorem 8.4.2
on the five intervals cut by the angles 0 < φ < θ < π/4 (Definition 8.4.1). The
explicit formulas of the five curves are Gerver's, solved from these ODEs in
[Ger92] and [Rom18]; this definition records the structural properties the
paper itself establishes for G in Theorem 8.4.1 and Theorem 8.4.2. Derivatives
are one-sided within each interval. -/
def IsGerverSofa (G : Set (ℝ × ℝ)) : Prop :=
  ∃ (φ θ : ℝ) (A B C D X : ℝ → ℝ × ℝ),
    0 < φ ∧ φ < θ ∧ θ < Real.pi / 4 ∧
    G = sofaOfPath X (Real.pi / 2) ∧
    IsMovingSofa G ∧
    ContDiffOn ℝ 1 X (Set.Icc 0 (Real.pi / 2)) ∧
    ContinuousOn A (Set.Icc 0 (Real.pi / 2)) ∧
    ContinuousOn C (Set.Icc 0 (Real.pi / 2)) ∧
    ContinuousOn B (Set.Icc (Real.pi / 2 - θ) (Real.pi / 2)) ∧
    ContinuousOn D (Set.Icc 0 θ) ∧
    (∀ t ∈ Set.Icc 0 (Real.pi / 2), dot (A t - X t) (u t) = 1) ∧
    (∀ t ∈ Set.Icc 0 (Real.pi / 2), dot (C t - X t) (v t) = 1) ∧
    (∀ t ∈ Set.Icc (Real.pi / 2 - θ) (Real.pi / 2), dot (B t - X t) (u t) = 0) ∧
    (∀ t ∈ Set.Icc 0 θ, dot (D t - X t) (v t) = 0) ∧
    (∀ t ∈ Set.Ioo 0 φ, dot (derivWithin A (Set.Ioo 0 φ) t) (v t) = 0) ∧
    (∀ t ∈ Set.Ioo 0 φ,
      dot (derivWithin D (Set.Ioo 0 φ) t) (u t)
        + dot (derivWithin C (Set.Ioo 0 φ) t) (u t) = 0) ∧
    (∀ t ∈ Set.Ioo φ θ,
      dot (derivWithin A (Set.Ioo φ θ) t) (v t)
        = dot (derivWithin X (Set.Ioo φ θ) t) (v t)) ∧
    (∀ t ∈ Set.Ioo φ θ,
      dot (derivWithin D (Set.Ioo φ θ) t) (u t)
        - dot (derivWithin X (Set.Ioo φ θ) t) (u t)
        + dot (derivWithin C (Set.Ioo φ θ) t) (u t) = 0) ∧
    (∀ t ∈ Set.Ioo θ (Real.pi / 2 - θ),
      dot (derivWithin A (Set.Ioo θ (Real.pi / 2 - θ)) t) (v t)
        = dot (derivWithin X (Set.Ioo θ (Real.pi / 2 - θ)) t) (v t)) ∧
    (∀ t ∈ Set.Ioo θ (Real.pi / 2 - θ),
      dot (derivWithin C (Set.Ioo θ (Real.pi / 2 - θ)) t) (u t)
        - dot (derivWithin X (Set.Ioo θ (Real.pi / 2 - θ)) t) (u t) = 0) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ),
      dot (derivWithin A (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ)) t) (v t)
        = dot (derivWithin X (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ)) t) (v t)
          - dot (derivWithin B (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ)) t) (v t)) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ),
      dot (derivWithin C (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ)) t) (u t)
        - dot (derivWithin X (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2 - φ)) t) (u t) = 0) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - φ) (Real.pi / 2),
      dot (derivWithin A (Set.Ioo (Real.pi / 2 - φ) (Real.pi / 2)) t) (v t)
        + dot (derivWithin B (Set.Ioo (Real.pi / 2 - φ) (Real.pi / 2)) t) (v t) = 0) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - φ) (Real.pi / 2),
      dot (derivWithin C (Set.Ioo (Real.pi / 2 - φ) (Real.pi / 2)) t) (u t) = 0) ∧
    (∀ t ∈ Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2),
      dot (derivWithin B (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) t) (u t) = 0 ∧
      dot (derivWithin B (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) t) (v t) < 0) ∧
    (∀ t ∈ Set.Ioo 0 θ,
      dot (derivWithin D (Set.Ioo 0 θ) t) (v t) = 0 ∧
      dot (derivWithin D (Set.Ioo 0 θ) t) (u t) > 0)

end Gerver


