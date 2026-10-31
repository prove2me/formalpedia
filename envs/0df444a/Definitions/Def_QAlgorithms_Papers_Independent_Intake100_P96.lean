-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P96
-- name    : QAlgorithms_Papers_Independent_Intake100_P96
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:55:21.720709+00:00
-- url     : https://prove2.me/theorems/d38a2c4d-97e3-49d4-8635-788a30f2b409
-- title:
--   Definitions for Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory
-- statement:
--   The objects the formalized statements of *Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory* (arXiv:hep-th/0312154) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RealModel`: Finite-dimensional real coordinate model, including dimension zero.
--   - `realModel`: The identity model with no boundary or corners.
--   - `SmoothGeometry`: Smooth Hausdorff/paracompact manifold convention, PDF pp. 3–4. Finite dimension is carried by the coordinate model. No nonemptiness, connectedness, or compactness is assumed.
--   - `HasSmoothLocalCoordinates`: Actual smooth local coordinates for a fibrewise action, PDF pp. 4, 7–8. The section and coordinate function are total extensions; every coordinate identity is restricted to the indicated open set. The resulting local trivialization is (x,h) ↦ action h (section x), with inverse (projection,coordinate). The same predicate describes a right bundle using action h e = e ◁ h.
--   - `LeftPrincipalBundle`: Left principal H-bundle in the convention of Definition 1, PDF p. 4. Freeness and transitivity are simultaneous uniqueness on each fibre; smooth local trivializations, smooth projection/action, and the real Lie group structure are data rather than conclusions assumed in any theorem.
--   - `RightPrincipalStructure`: The additional RIGHT principal action, Definition 1 and (1), PDF p. 4. Right local coordinates are required as well; no right-principality conclusion is hidden in a left-action axiom.
--   - `IsCentralSection`: A smooth global central section in (3), PDF p. 4.
--   - `IsTrivialBibundle`: Triviality means a smooth bibundle isomorphism with M × H, PDF p. 4. It is defined by independent inverse maps, base preservation, and both standard actions, rather than by the central-section criterion being stated.
--   - `phiValue`: The actual automorphism's value is the unique left multiplier in (4), PDF p. 5. This definition is only a function; its automorphism properties are not assumed in its body.
--   - `IsBibundleMap`: Smooth base-preserving map compatible with both actions, (2), PDF p. 4.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, https://arxiv.org/abs/hep-th/0312154v2

import Mathlib

/-!
Paper-local smooth principal-bibundle statements from hep-th/0312154v2, §2.
All result proofs are intentionally omitted. The differential-geometric and
quotient constructions required by the remaining nodes are explicitly deferred
in this unit's HARD.md and GAPS.json; they are not abstract proposition fields.
Compilation is pending the batch mechanical handoff.
-/

open scoped Manifold ContDiff

namespace QAlgorithms.Papers.Independent.Intake100.P96

universe u v w z

/-- Finite-dimensional real coordinate model, including dimension zero. -/
abbrev RealModel (n : ℕ) := Fin n → ℝ

/-- The identity model with no boundary or corners. -/
noncomputable abbrev realModel (n : ℕ) := 𝓘(ℝ, RealModel n)

/-- Smooth Hausdorff/paracompact manifold convention, PDF pp. 3–4.
Finite dimension is carried by the coordinate model. No nonemptiness,
connectedness, or compactness is assumed. -/
structure SmoothGeometry (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (RealModel n) X] : Prop where
  smoothAtlas : IsManifold (realModel n) ∞ X
  hausdorff : T2Space X
  paracompact : ParacompactSpace X

/-- Sanity: ordinary finite-dimensional real space satisfies the convention. -/
example (n : ℕ) : SmoothGeometry n (RealModel n) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section Bundles

variable {m h e : ℕ} {M : Type u} {H : Type v} {E : Type w}
variable [TopologicalSpace M] [ChartedSpace (RealModel m) M]
variable [TopologicalSpace H] [ChartedSpace (RealModel h) H]
variable [TopologicalSpace E] [ChartedSpace (RealModel e) E]
variable [Group H]

/-- Actual smooth local coordinates for a fibrewise action, PDF pp. 4, 7–8.
The section and coordinate function are total extensions; every coordinate
identity is restricted to the indicated open set. The resulting local
trivialization is (x,h) ↦ action h (section x), with inverse (projection,coordinate).
The same predicate describes a right bundle using action h e = e ◁ h. -/
def HasSmoothLocalCoordinates (projection : E → M) (action : H → E → E) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ sectionMap : M → E, ∃ coordinate : E → H,
      ContMDiffOn (realModel m) (realModel e) ∞ sectionMap U ∧
      ContMDiffOn (realModel e) (realModel h) ∞ coordinate (projection ⁻¹' U) ∧
      (∀ y ∈ U, projection (sectionMap y) = y) ∧
      (∀ q : E, projection q ∈ U →
        action (coordinate q) (sectionMap (projection q)) = q) ∧
      (∀ y ∈ U, ∀ k : H, coordinate (action k (sectionMap y)) = k)

/-- Left principal H-bundle in the convention of Definition 1, PDF p. 4.
Freeness and transitivity are simultaneous uniqueness on each fibre; smooth
local trivializations, smooth projection/action, and the real Lie group
structure are data rather than conclusions assumed in any theorem. -/
structure LeftPrincipalBundle (m h e : ℕ) (M : Type u) (H : Type v) (E : Type w)
    [TopologicalSpace M] [ChartedSpace (RealModel m) M]
    [TopologicalSpace H] [ChartedSpace (RealModel h) H]
    [TopologicalSpace E] [ChartedSpace (RealModel e) E] [Group H] where
  baseGeometry : SmoothGeometry m M
  groupGeometry : SmoothGeometry h H
  totalGeometry : SmoothGeometry e E
  lieGroup : LieGroup (realModel h) ∞ H
  projection : E → M
  leftAction : H → E → E
  smoothProjection : ContMDiff (realModel e) (realModel m) ∞ projection
  smoothLeftAction : ContMDiff ((realModel h).prod (realModel e)) (realModel e) ∞
    (fun q : H × E => leftAction q.1 q.2)
  oneAction : ∀ q : E, leftAction 1 q = q
  mulAction : ∀ k l : H, ∀ q : E,
    leftAction (k * l) q = leftAction k (leftAction l q)
  projectionLeft : ∀ k : H, ∀ q : E, projection (leftAction k q) = projection q
  fibreTorsor : ∀ q r : E, projection q = projection r →
    ∃! k : H, leftAction k q = r
  localCoordinates : HasSmoothLocalCoordinates (m := m) (h := h) (e := e)
    projection leftAction

/-- The additional RIGHT principal action, Definition 1 and (1), PDF p. 4.
Right local coordinates are required as well; no right-principality conclusion
is hidden in a left-action axiom. -/
structure RightPrincipalStructure (B : LeftPrincipalBundle m h e M H E) where
  rightAction : E → H → E
  smoothRightAction : ContMDiff ((realModel e).prod (realModel h)) (realModel e) ∞
    (fun q : E × H => rightAction q.1 q.2)
  oneAction : ∀ q : E, rightAction q 1 = q
  mulAction : ∀ q : E, ∀ k l : H,
    rightAction q (k * l) = rightAction (rightAction q k) l
  projectionRight : ∀ q : E, ∀ k : H,
    B.projection (rightAction q k) = B.projection q
  fibreTorsor : ∀ q r : E, B.projection q = B.projection r →
    ∃! k : H, rightAction q k = r
  commute : ∀ k l : H, ∀ q : E,
    rightAction (B.leftAction k q) l = B.leftAction k (rightAction q l)
  localCoordinates : HasSmoothLocalCoordinates (m := m) (h := h) (e := e)
    B.projection (fun k q => rightAction q k)

/-- A smooth global central section in (3), PDF p. 4. -/
def IsCentralSection (B : LeftPrincipalBundle m h e M H E)
    (R : RightPrincipalStructure B) (s : M → E) : Prop :=
  ContMDiff (realModel m) (realModel e) ∞ s ∧
    (∀ x : M, B.projection (s x) = x) ∧
    (∀ k : H, ∀ x : M, B.leftAction k (s x) = R.rightAction (s x) k)

/-- Triviality means a smooth bibundle isomorphism with M × H, PDF p. 4.
It is defined by independent inverse maps, base preservation, and both
standard actions, rather than by the central-section criterion being stated. -/
def IsTrivialBibundle (B : LeftPrincipalBundle m h e M H E)
    (R : RightPrincipalStructure B) : Prop :=
  ∃ W : M × H → E, ∃ V : E → M × H,
    ContMDiff ((realModel m).prod (realModel h)) (realModel e) ∞ W ∧
    ContMDiff (realModel e) ((realModel m).prod (realModel h)) ∞ V ∧
    Function.LeftInverse V W ∧ Function.RightInverse V W ∧
    (∀ x : M, ∀ k : H, B.projection (W (x, k)) = x) ∧
    (∀ x : M, ∀ k l : H, W (x, k * l) = B.leftAction k (W (x, l))) ∧
    (∀ x : M, ∀ k l : H, W (x, k * l) = R.rightAction (W (x, k)) l)

/-- The actual automorphism's value is the unique left multiplier in (4),
PDF p. 5. This definition is only a function; its automorphism properties
are not assumed in its body. -/
noncomputable def phiValue (B : LeftPrincipalBundle m h e M H E)
    (R : RightPrincipalStructure B) (q : E) (k : H) : H :=
  Classical.choose (B.fibreTorsor q (R.rightAction q k) (R.projectionRight q k).symm).exists

/-- Sanity: the chosen multiplier satisfies exactly the defining equation (4). -/
example (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B)
    (q : E) (k : H) : B.leftAction (phiValue B R q k) q = R.rightAction q k := by
  exact Classical.choose_spec
    (B.fibreTorsor q (R.rightAction q k) (R.projectionRight q k).symm).exists

section Morphisms

variable {d : ℕ} {F : Type z}
variable [TopologicalSpace F] [ChartedSpace (RealModel d) F]

/-- Smooth base-preserving map compatible with both actions, (2), PDF p. 4. -/
def IsBibundleMap (B : LeftPrincipalBundle m h e M H E)
    (R : RightPrincipalStructure B) (C : LeftPrincipalBundle m h d M H F)
    (S : RightPrincipalStructure C) (W : E → F) : Prop :=
  ContMDiff (realModel e) (realModel d) ∞ W ∧
    (∀ q : E, C.projection (W q) = B.projection q) ∧
    (∀ k : H, ∀ q : E, W (B.leftAction k q) = C.leftAction k (W q)) ∧
    (∀ q : E, ∀ k : H, W (R.rightAction q k) = S.rightAction (W q) k)

/-- Sanity: the identity is a smooth bibundle morphism, with both action laws. -/
example (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B) :
    IsBibundleMap B R B R id := by
  exact ⟨contMDiff_id, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Morphisms

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96


