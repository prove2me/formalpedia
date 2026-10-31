-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P03
-- name    : QAlgorithms_Papers_Independent_Intake100_P03
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:41:27.724086+00:00
-- url     : https://prove2.me/theorems/9ceaf02f-96e6-4a9b-b7bc-b9d9a0736b12
-- title:
--   Definitions for The Classifying Space of a Topological 2-Group
-- statement:
--   The objects the formalized statements of *The Classifying Space of a Topological 2-Group* (arXiv:0801.3843) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsKSpace`: PDF p. 5: a compactly generated weak Hausdorff space. Weak Hausdorff means that every continuous image of a compact Hausdorff space is closed. The compact test spaces and all spaces in the statement lie in universe u.
--   - `KContinuousTwo`: PDF pp. 5, 8: continuity of a binary map on the k-product. Compact Hausdorff probes into the ordinary product are pairs of continuous maps. This does not demand continuity on the ordinary product of arbitrary spaces.
--   - `IsKGroup`: PDF pp. 5, 8: a group object in compactly generated weak Hausdorff spaces, with multiplication continuous on the k-product.
--   - `TopologicalCrossedModule`: PDF pp. 8--9, equations (4),(5): topological crossed-module data. The homomorphism rho supplies an action by automorphisms; continuity is joint k-product continuity. No condition on injectivity of boundary is added.
--   - `OpenCover`: PDF p. 12: an arbitrary indexed open cover; the index type may be empty. In that case the coverage condition forces the base space to be empty.
--   - `overlapTwo`: PDF pp. 12--15: the double overlap with its subspace topology.
--   - `overlapThree`: PDF pp. 13--15: the triple overlap with its subspace topology.
--   - `CechCocycle`: PDF pp. 13--14: normalized continuous weak 2-functor coordinates. The tetrahedron follows equation (6) using vertical composition hprime*h from PDF p. 12, correcting the reversed factor order in printed equation (2). The source explicitly normalizes h to one whenever any two indices agree.
--   - `trivialCocycle`: PDF p. 16: the actual trivial cocycle on any open cover.
--   - `CechTransformation`: PDF pp. 14--15, equation (3) and prism (7): an actual continuous weak natural isomorphism between the given cocycles. The prism is written with the same later-factor-on-the-left vertical composition as the source. The unit law is k_ii=1; this is not an equivalence closure.
--   - `Cohomologous`: PDF p. 15: cohomologousness is existence of continuous f_i and k_ij satisfying the square, prism, and unit. No quotient is presumed to exist.
--   - `identityTransformation`: PDF pp. 14--15: the identity weak natural isomorphism, used as a sanity check of the square, prism orientation, and repeated-index unit.
-- source:
--   The Classifying Space of a Topological 2-Group, arXiv:0801.3843v2, https://arxiv.org/abs/0801.3843v2

import Mathlib

/-!
Statements from Baez--Stevenson, arXiv:0801.3843v2.
Only the fixed-cover equivalence-relation node is stated. All other planned
nodes are accounted for in this unit's HARD.md and GAPS.json.

New definitions implement the complete fixed-cover crossed-module coordinates.
Binary continuity is tested on compact Hausdorff spaces, so it is continuity
on the k-product, without an extra ordinary-product continuity assumption.
The tetrahedron equation follows the diagrams and the vertical composition
rule on PDF p. 12; the printed scalar equation has its factors reversed.
Correction E2 was independently checked in moderation round 1. Compilation
is pending handoff; review-record edits require a fresh moderation round.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P03

universe u

/-- PDF p. 5: a compactly generated weak Hausdorff space. Weak Hausdorff
means that every continuous image of a compact Hausdorff space is closed.
The compact test spaces and all spaces in the statement lie in universe u. -/
def IsKSpace (X : Type u) [TopologicalSpace X] : Prop :=
  CompactlyGeneratedSpace X ∧
    ∀ (S : CompHaus.{u}) (f : C(S, X)), IsClosed (Set.range f)

/-- PDF pp. 5, 8: continuity of a binary map on the k-product. Compact
Hausdorff probes into the ordinary product are pairs of continuous maps.
This does not demand continuity on the ordinary product of arbitrary spaces. -/
def KContinuousTwo {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y → Z) : Prop :=
  ∀ (S : CompHaus.{u}) (a : C(S, X)) (b : C(S, Y)),
    Continuous (fun s => f (a s) (b s))

/-- Sanity: the first k-product projection is continuous. -/
example (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    KContinuousTwo (fun (x : X) (_ : Y) => x) := by
  intro S a b
  exact a.continuous

/-- PDF pp. 5, 8: a group object in compactly generated weak Hausdorff
spaces, with multiplication continuous on the k-product. -/
def IsKGroup (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  IsKSpace G ∧ KContinuousTwo (fun (a b : G) => a * b) ∧
    Continuous (fun a : G => a⁻¹)

/-- PDF pp. 8--9, equations (4),(5): topological crossed-module data.
The homomorphism rho supplies an action by automorphisms; continuity is
joint k-product continuity. No condition on injectivity of boundary is added. -/
structure TopologicalCrossedModule (G H : Type u)
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] where
  boundary : H →* G
  rho : G →* MulAut H
  objectGroup : IsKGroup G
  arrowKernelGroup : IsKGroup H
  boundaryContinuous : Continuous boundary
  actionContinuous : KContinuousTwo (fun g h => rho g h)
  equivariance : ∀ g h, boundary (rho g h) = g * boundary h * g⁻¹
  peiffer : ∀ h k, rho (boundary h) k = h * k * h⁻¹

/-- PDF p. 12: an arbitrary indexed open cover; the index type may be empty.
In that case the coverage condition forces the base space to be empty. -/
structure OpenCover (M I : Type u) [TopologicalSpace M] where
  opens : I → Set M
  isOpen : ∀ i, IsOpen (opens i)
  covers : ∀ x : M, ∃ i, x ∈ opens i

/-- PDF pp. 12--15: the double overlap with its subspace topology. -/
abbrev overlapTwo {M I : Type u} [TopologicalSpace M] (U : OpenCover M I)
    (i j : I) :=
  {x : M // x ∈ U.opens i ∧ x ∈ U.opens j}

/-- PDF pp. 13--15: the triple overlap with its subspace topology. -/
abbrev overlapThree {M I : Type u} [TopologicalSpace M] (U : OpenCover M I)
    (i j k : I) :=
  {x : M // x ∈ U.opens i ∧ x ∈ U.opens j ∧ x ∈ U.opens k}

/-- PDF pp. 13--14: normalized continuous weak 2-functor coordinates.
The tetrahedron follows equation (6) using vertical composition hprime*h
from PDF p. 12, correcting the reversed factor order in printed equation (2).
The source explicitly normalizes h to one whenever any two indices agree. -/
structure CechCocycle {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] (C : TopologicalCrossedModule G H)
    (U : OpenCover M I) where
  g : ∀ i j, C(overlapTwo U i j, G)
  h : ∀ i j k, C(overlapThree U i j k, H)
  triangle : ∀ i j k (x : M) (hi : x ∈ U.opens i)
      (hj : x ∈ U.opens j) (hk : x ∈ U.opens k),
    C.boundary (h i j k ⟨x, hi, hj, hk⟩) *
      g i j ⟨x, hi, hj⟩ * g j k ⟨x, hj, hk⟩ = g i k ⟨x, hi, hk⟩
  tetrahedron : ∀ i j k l (x : M) (hi : x ∈ U.opens i)
      (hj : x ∈ U.opens j) (hk : x ∈ U.opens k) (hl : x ∈ U.opens l),
    h i k l ⟨x, hi, hk, hl⟩ * h i j k ⟨x, hi, hj, hk⟩ =
      h i j l ⟨x, hi, hj, hl⟩ *
        C.rho (g i j ⟨x, hi, hj⟩) (h j k l ⟨x, hj, hk, hl⟩)
  unitG : ∀ i (x : M) (hi : x ∈ U.opens i), g i i ⟨x, hi, hi⟩ = 1
  unitH : ∀ i j k (x : M) (hi : x ∈ U.opens i)
      (hj : x ∈ U.opens j) (hk : x ∈ U.opens k),
    (i = j ∨ j = k ∨ i = k) → h i j k ⟨x, hi, hj, hk⟩ = 1

/-- PDF p. 16: the actual trivial cocycle on any open cover. -/
def trivialCocycle {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] (C : TopologicalCrossedModule G H)
    (U : OpenCover M I) : CechCocycle C U where
  g := fun _ _ => ⟨fun _ => 1, continuous_const⟩
  h := fun _ _ _ => ⟨fun _ => 1, continuous_const⟩
  triangle := by intros; simp
  tetrahedron := by intros; simp
  unitG := by intros; rfl
  unitH := by intros; rfl

/-- Sanity: the distinguished cocycle has identity transition functions. -/
example {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] (C : TopologicalCrossedModule G H)
    (U : OpenCover M I) (i j : I) (x : overlapTwo U i j) :
    (trivialCocycle C U).g i j x = 1 := rfl

/-- PDF pp. 14--15, equation (3) and prism (7): an actual continuous
weak natural isomorphism between the given cocycles. The prism is written
with the same later-factor-on-the-left vertical composition as the source.
The unit law is k_ii=1; this is not an equivalence closure. -/
structure CechTransformation {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] {C : TopologicalCrossedModule G H}
    {U : OpenCover M I} (a b : CechCocycle C U) where
  f : ∀ i, C({x : M // x ∈ U.opens i}, G)
  k : ∀ i j, C(overlapTwo U i j, H)
  square : ∀ i j (x : M) (hi : x ∈ U.opens i) (hj : x ∈ U.opens j),
    C.boundary (k i j ⟨x, hi, hj⟩) * a.g i j ⟨x, hi, hj⟩ * f j ⟨x, hj⟩ =
      f i ⟨x, hi⟩ * b.g i j ⟨x, hi, hj⟩
  prism : ∀ i j l (x : M) (hi : x ∈ U.opens i)
      (hj : x ∈ U.opens j) (hl : x ∈ U.opens l),
    k i l ⟨x, hi, hl⟩ * a.h i j l ⟨x, hi, hj, hl⟩ =
      C.rho (f i ⟨x, hi⟩) (b.h i j l ⟨x, hi, hj, hl⟩) *
        k i j ⟨x, hi, hj⟩ *
          C.rho (a.g i j ⟨x, hi, hj⟩) (k j l ⟨x, hj, hl⟩)
  unit : ∀ i (x : M) (hi : x ∈ U.opens i), k i i ⟨x, hi, hi⟩ = 1

/-- PDF p. 15: cohomologousness is existence of continuous f_i and k_ij
satisfying the square, prism, and unit. No quotient is presumed to exist. -/
def Cohomologous {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] {C : TopologicalCrossedModule G H}
    {U : OpenCover M I} (a b : CechCocycle C U) : Prop :=
  Nonempty (CechTransformation a b)

/-- PDF pp. 14--15: the identity weak natural isomorphism, used as a
sanity check of the square, prism orientation, and repeated-index unit. -/
def identityTransformation {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] {C : TopologicalCrossedModule G H}
    {U : OpenCover M I} (a : CechCocycle C U) : CechTransformation a a where
  f := fun _ => ⟨fun _ => 1, continuous_const⟩
  k := fun _ _ => ⟨fun _ => 1, continuous_const⟩
  square := by intros; simp
  prism := by intros; simp
  unit := by intros; rfl

/-- Sanity: the raw relation contains the actual identity witness. -/
example {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] {C : TopologicalCrossedModule G H}
    {U : OpenCover M I} (a : CechCocycle C U) : Cohomologous a a :=
  ⟨identityTransformation a⟩

end QAlgorithms.Papers.Independent.Intake100.P03


