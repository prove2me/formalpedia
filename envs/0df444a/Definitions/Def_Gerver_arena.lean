-- Prove2me | Definitions.Def_Gerver_arena
-- name    : Gerver_arena
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T19:29:20.353804+00:00
-- url     : https://prove2.me/theorems/af595b23-417a-48fb-bbc0-ef4e41ce3bbd
-- title:
--   The hallway, moving sofas, and the maximum sofa area
-- statement:
--   The arena of the moving sofa problem. The hallway is the L-shaped union of the horizontal side (-∞, 1] × [0, 1] and the vertical side [0, 1] × (-∞, 1]: two unit-width corridors meeting at a right angle. A moving sofa is a nonempty, compact, connected planar shape that can be moved around the corner: there is a continuous path of orientation-preserving rigid motions of the plane, parametrized by the unit interval, whose initial term is a translation placing the shape inside the horizontal side, whose every term keeps the image of the shape inside the hallway, and whose final term places the image inside the vertical side. A movement of rotation angle ω is such a path whose total clockwise turn equals ω. The area of a planar set is its two-dimensional Lebesgue measure as a real number; the maximum sofa area α_max is the supremum of the areas of all moving sofas, and m_ω is the supremum taken over moving sofas admitting a movement of rotation angle ω.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Definitions 1.1.1-1.1.3 with footnote 3 and Definition 1.2.1

import Mathlib

namespace Gerver

/-- Counterclockwise rotation of the plane around the origin by the angle t
(Definition 1.2.2: R_t : ℝ² → ℝ²). -/
noncomputable def rot (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * Real.cos t - p.2 * Real.sin t, p.1 * Real.sin t + p.2 * Real.cos t)

/-- The horizontal side H_L = (-∞, 1] × [0, 1] of the hallway (Definition 1.1.1). -/
def hallH : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The vertical side V_L = [0, 1] × (-∞, 1] of the hallway (Definition 1.1.1). -/
def hallV : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- The hallway L = H_L ∪ V_L: the L-shaped union of two unit-width corridors
meeting at a right angle (Definition 1.1.1). -/
def hallway : Set (ℝ × ℝ) := hallH ∪ hallV

/-- The sofa S admits a movement of rotation angle ω through the hallway
(Definition 1.1.2 with its footnote 3; the rotation angle of Definition 1.2.1):
there is a continuous path t ↦ Φ_t of orientation-preserving rigid motions
Φ_t(p) = rot (Θ t) p + V t, parametrized by t ∈ [0, 1], with Φ_0 the
translation p ↦ p + V 0 putting S inside the horizontal side, Φ_t(S) ⊆ L for
all t ∈ [0, 1], Φ_1(S) ⊆ V_L, and total clockwise rotation -Θ 1 = ω. -/
def HasMovementAngle (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  ∃ (Θ : ℝ → ℝ) (W : ℝ → ℝ × ℝ),
    Θ 0 = 0 ∧ Continuous Θ ∧ Continuous W ∧
    (fun p => p + W 0) '' S ⊆ hallH ∧
    (∀ t ∈ Set.Icc 0 1, (fun p => rot (Θ t) p + W t) '' S ⊆ hallway) ∧
    (fun p => rot (Θ 1) p + W 1) '' S ⊆ hallV ∧
    -Θ 1 = ω

/-- The sofa S can move around the corner: it admits a movement of some
rotation angle (Definition 1.1.2). -/
def HasMovement (S : Set (ℝ × ℝ)) : Prop := ∃ ω, HasMovementAngle S ω

/-- A moving sofa: a nonempty, compact, connected shape that can move around
the corner of the hallway (Definition 1.1.2, with the paper's standing
convention — adopted from Chapter 2 — that a shape is a nonempty compact
subset of the plane). -/
def IsMovingSofa (S : Set (ℝ × ℝ)) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ IsConnected S ∧ HasMovement S

/-- The two-dimensional Lebesgue measure on the plane: the area functional of
Definition 1.1.3 assigns to a Borel set X its two-dimensional volume. -/
noncomputable def vol2 : MeasureTheory.Measure (ℝ × ℝ) :=
  MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.volume

/-- The area |X| of a planar set, as a real number (Definition 1.1.3). -/
noncomputable def area (X : Set (ℝ × ℝ)) : ℝ := (vol2 X).toReal

/-- The maximum sofa area α_max: the supremum of the areas of all moving
sofas (the quantity asked for by the moving sofa problem). -/
noncomputable def sofaMax : ℝ := sSup {r | ∃ S, IsMovingSofa S ∧ area S = r}

/-- The maximum area m_ω among moving sofas that admit a movement of rotation
angle ω (the quantity maximized in Theorem 3.5.6). -/
noncomputable def angleMax (ω : ℝ) : ℝ :=
  sSup {r | ∃ S, IsMovingSofa S ∧ HasMovementAngle S ω ∧ area S = r}

end Gerver


