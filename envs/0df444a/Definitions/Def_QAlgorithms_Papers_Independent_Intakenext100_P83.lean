-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P83
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P83
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:08:54.264439+00:00
-- url     : https://prove2.me/theorems/4dec0743-2d62-494f-be19-04a61f0a7692
-- title:
--   Definitions for Two-Categorical Bundles and Their Classifying Spaces
-- statement:
--   The objects the formalized statements of *Two-Categorical Bundles and Their Classifying Spaces* (arXiv:math/0612549) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CylinderCorner`: The cylinder corner `{0} × X ∪ I × range(i)` with the subspace topology. This is the retract formulation of the homotopy extension property used in §5, PDF pp. 20–21. The interval is the closed real unit interval.
--   - `IsClosedCofibration`: A closed cofibration is a closed embedding with the homotopy extension property. We use the equivalent cylinder-corner retraction criterion: a continuous retraction of `I × X` onto `{0} × X ∪ I × range(i)`. The closed embedding ensures that the corner's subspace topology agrees with the topology used for pasting homotopies. Source: §5, PDF pp. 20–21.
--   - `IsLocallyEquiconnected`: Definition of locally equiconnected in §5, PDF p. 20: the diagonal is a closed cofibration. No separation axiom is silently imposed.
--   - `IsGood`: Definition of good simplicial space, PDF p. 51: every degeneracy is a closed cofibration. `SimplicialObject TopCat` carries every simplicial identity and continuity of all structure maps.
--   - `FiniteOrderedOpenCover`: A finite totally ordered open cover. Section 6, PDF pp. 29–30 and 36, requires nonempty members. The index type itself may be empty when the base space is empty. We retain arbitrary finite linear orders, rather than fixing an enumeration or changing a partial order on unrelated general covers.
--   - `CechChain`: Strictly increasing index chains of length `k + 1`, PDF p. 38.
--   - `NondegenerateCech`: The nondegenerate ordered Čech space `N_k`, PDF p. 38. The dependent sum has the coproduct topology, and each intersection has its subspace topology. Different index chains remain different summands even if their intersections are the same subset of the base.
--   - `cechFace`: Face map deleting the indicated vertex in a strictly increasing chain, with its underlying base point unchanged. PDF p. 38.
--   - `FaceImage`: The union of the images of all face maps, with its subspace topology; this is the paper's `L^k N`, not a Reedy latching object. PDF pp. 38–39.
--   - `faceUnion`: The canonical map from the disjoint union of the face domains onto the face-image union, PDF p. 38. Its domain uses the coproduct topology.
-- source:
--   Two-Categorical Bundles and Their Classifying Spaces, arXiv:math/0612549v2, https://arxiv.org/abs/math/0612549v2

import Mathlib

/-!
Statements from Baas, Bökstedt, and Kro, arXiv:math/0612549v2.
Only the four results whose complete interfaces are supplied below are drafted.
The other planned nodes are explicitly accounted for in the unit's HARD.md.
-/

open CategoryTheory
open scoped Simplicial

namespace QAlgorithms.Papers.Independent.Intakenext100.P83

universe u v

/-- The cylinder corner `{0} × X ∪ I × range(i)` with the subspace topology.
This is the retract formulation of the homotopy extension property used in §5,
PDF pp. 20–21. The interval is the closed real unit interval. -/
abbrev CylinderCorner {A : Type u} {X : Type v} (i : A → X) :=
  {p : unitInterval × X // p.1 = 0 ∨ p.2 ∈ Set.range i}

/-- A closed cofibration is a closed embedding with the homotopy extension
property. We use the equivalent cylinder-corner retraction criterion: a
continuous retraction of `I × X` onto `{0} × X ∪ I × range(i)`.
The closed embedding ensures that the corner's subspace topology agrees with
the topology used for pasting homotopies. Source: §5, PDF pp. 20–21. -/
def IsClosedCofibration {A : Type u} {X : Type v}
    [TopologicalSpace A] [TopologicalSpace X] (i : A → X) : Prop :=
  Topology.IsClosedEmbedding i ∧
    ∃ r : C(unitInterval × X, CylinderCorner i),
      ∀ z : CylinderCorner i, r z.val = z

/-- Definition of locally equiconnected in §5, PDF p. 20: the diagonal is a
closed cofibration. No separation axiom is silently imposed. -/
def IsLocallyEquiconnected (X : Type u) [TopologicalSpace X] : Prop :=
  IsClosedCofibration (fun x : X => (x, x))

/-- Definition of good simplicial space, PDF p. 51: every degeneracy is a
closed cofibration. `SimplicialObject TopCat` carries every simplicial identity
and continuity of all structure maps. -/
def IsGood (Z : SimplicialObject TopCat.{u}) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 1)),
    IsClosedCofibration (Z.σ i : Z _⦋n⦌ → Z _⦋n + 1⦌)

/-- Sanity check for the cylinder-corner definition: identity inclusions have
HEP, including on the empty space. -/
example (X : Type u) [TopologicalSpace X] :
    IsClosedCofibration (id : X → X) := by
  refine ⟨Topology.IsClosedEmbedding.id, ?_⟩
  refine ⟨⟨fun p => ⟨p, Or.inr ⟨p.2, rfl⟩⟩,
    continuous_id.subtype_mk _⟩, ?_⟩
  intro z
  apply Subtype.ext
  rfl

/-- A finite totally ordered open cover. Section 6, PDF pp. 29–30 and 36,
requires nonempty members. The index type itself may be empty when the base
space is empty. We retain arbitrary finite linear orders, rather than fixing
an enumeration or changing a partial order on unrelated general covers. -/
structure FiniteOrderedOpenCover (X : Type u) [TopologicalSpace X]
    (Index : Type v) [LinearOrder Index] [Fintype Index] where
  member : Index → Set X
  openMember : ∀ a, IsOpen (member a)
  nonemptyMember : ∀ a, (member a).Nonempty
  covers : ∀ x : X, ∃ a, x ∈ member a

/-- Strictly increasing index chains of length `k + 1`, PDF p. 38. -/
abbrev CechChain (Index : Type v) [LinearOrder Index] (k : ℕ) :=
  {a : Fin (k + 1) → Index // StrictMono a}

/-- The nondegenerate ordered Čech space `N_k`, PDF p. 38. The dependent sum
has the coproduct topology, and each intersection has its subspace topology.
Different index chains remain different summands even if their intersections
are the same subset of the base. -/
abbrev NondegenerateCech {X : Type u} [TopologicalSpace X]
    {Index : Type v} [LinearOrder Index] [Fintype Index]
    (U : FiniteOrderedOpenCover X Index) (k : ℕ) :=
  Σ a : CechChain Index k, {x : X // ∀ j, x ∈ U.member (a.val j)}

/-- Face map deleting the indicated vertex in a strictly increasing chain,
with its underlying base point unchanged. PDF p. 38. -/
def cechFace {X : Type u} [TopologicalSpace X]
    {Index : Type v} [LinearOrder Index] [Fintype Index]
    (U : FiniteOrderedOpenCover X Index) {k : ℕ} (i : Fin (k + 2))
    (x : NondegenerateCech U (k + 1)) : NondegenerateCech U k :=
  ⟨⟨fun j => x.1.val (i.succAbove j),
      x.1.property.comp (Fin.strictMono_succAbove i)⟩,
    ⟨x.2.val, fun j => x.2.property (i.succAbove j)⟩⟩

/-- The union of the images of all face maps, with its subspace topology;
this is the paper's `L^k N`, not a Reedy latching object. PDF pp. 38–39. -/
def FaceImage {X : Type u} [TopologicalSpace X]
    {Index : Type v} [LinearOrder Index] [Fintype Index]
    (U : FiniteOrderedOpenCover X Index) (k : ℕ) : Set (NondegenerateCech U k) :=
  {x | ∃ (i : Fin (k + 2)) (y : NondegenerateCech U (k + 1)), cechFace U i y = x}

/-- The canonical map from the disjoint union of the face domains onto the
face-image union, PDF p. 38. Its domain uses the coproduct topology. -/
def faceUnion {X : Type u} [TopologicalSpace X]
    {Index : Type v} [LinearOrder Index] [Fintype Index]
    (U : FiniteOrderedOpenCover X Index) (k : ℕ)
    (y : Σ _i : Fin (k + 2), NondegenerateCech U (k + 1)) : FaceImage U k :=
  ⟨cechFace U y.1 y.2, ⟨y.1, y.2, rfl⟩⟩

/-- Sanity check for the Čech face maps: deleting a vertex preserves the
underlying point of the base space. -/
example {X : Type u} [TopologicalSpace X]
    {Index : Type v} [LinearOrder Index] [Fintype Index]
    (U : FiniteOrderedOpenCover X Index) {k : ℕ} (i : Fin (k + 2))
    (x : NondegenerateCech U (k + 1)) :
    (cechFace U i x).2.val = x.2.val := by
  rfl

end QAlgorithms.Papers.Independent.Intakenext100.P83


