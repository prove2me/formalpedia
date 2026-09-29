-- Prove2me | Definitions.Def_LeanEval_SpaceGroups_Definitions
-- name    : LeanEval_SpaceGroups_Definitions
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-06T02:38:06.608047+00:00
-- url     : https://prove2.me/theorems/4651f0ab-1ce1-4370-8382-90021eb89e0a
-- title:
--   LeanEval crystallographic groups, affine equivalences, and counting functions
-- statement:
--   For every natural dimension $d$, let $E_d$ be real Euclidean space, and consider subgroups of its affine isometry group. A group satisfies the discrete condition when, for every point $x$ and every real $\varepsilon>0$, only finitely many of its elements move $x$ by distance at most $\varepsilon$. It is crystallographic when it also contains translations by the members of some linearly independent family of $d$ vectors.
--
--   Two such groups are affinely equivalent when conjugation by an invertible affine map identifies their sets of affine transformations. The orientation-preserving version additionally requires that conjugating map to have positive linear determinant. An isometry is orientation-preserving precisely when its own linear determinant is positive.
--
--   The three counting functions take extended-natural cardinalities of the sets of distinct equivalence-class subsets: unrestricted affine equivalence; orientation-preserving affine equivalence; and orientation-preserving affine equivalence restricted to crystallographic groups all of whose elements preserve orientation. They do not prescribe any numerical answer, assume a classification, or identify groups by a supplied finite list. This bundle provides exactly the reusable definitions needed by the goal.
-- source:
--   LeanEval v1, statement revision 1, problem space_groups_230; LeanEval/Geometry/SpaceGroups.lean, LeanEval.Geometry.SpaceGroupsProblem.space_groups, repository commit 296b7491ec989d21bcf8636a9a69231a1e5d1d25: https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/SpaceGroups.lean . Metadata: manifests/problems/space_groups_230.toml at the same commit. Background: Oliver Knill, Some Fundamental Theorems in Mathematics, section 94 (Crystallography), printed p. 41, version last updated June 25, 2023, https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf . The exact LeanEval definitions, not the background prose alone, govern this target.

import Mathlib

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

/-- The Euclidean model space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Euclidean motion group `E_d`. -/
abbrev EuclideanIsom (d : ℕ) := E d ≃ᵃⁱ[ℝ] E d

/-- The affine group `Aff(ℝᵈ)`. -/
abbrev AffineGroup (d : ℕ) := E d ≃ᵃ[ℝ] E d

/-- `g ∈ E_d` is **translation by `v`**. -/
def IsTranslationBy {d : ℕ} (g : EuclideanIsom d) (v : E d) : Prop :=
  ∀ x : E d, g x = x + v

/-- A subgroup `G ≤ E_d` is **discrete** in the proper-discontinuity
sense. -/
def IsDiscrete {d : ℕ} (G : Subgroup (EuclideanIsom d)) : Prop :=
  ∀ x : E d, ∀ ε > (0 : ℝ),
    {g : EuclideanIsom d | g ∈ G ∧ dist (g x) x ≤ ε}.Finite

/-- A subgroup `G ≤ E_d` is **crystallographic**: discrete and contains
`d` linearly independent translations. -/
structure IsCrystallographicGroup {d : ℕ} (G : Subgroup (EuclideanIsom d)) : Prop where
  discrete : IsDiscrete G
  cocompact : ∃ v : Fin d → E d, LinearIndependent ℝ v ∧
    ∀ i, ∃ g : EuclideanIsom d, g ∈ G ∧ IsTranslationBy g (v i)

/-- The set of crystallographic groups in dimension `d`. -/
def CrystallographicGroup (d : ℕ) : Type :=
  { G : Subgroup (EuclideanIsom d) // IsCrystallographicGroup G }

/-- An affine isometry is **orientation-preserving** if its linear part
has positive determinant. -/
def IsOrientationPreservingIsom {d : ℕ} (g : EuclideanIsom d) : Prop :=
  0 < (g.toAffineEquiv.linear.det : ℝ)

/-- Two subgroups `G₁, G₂ ≤ E_d` are **affinely equivalent**. -/
def AffinelyEquivalent {d : ℕ} (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  ∃ φ : AffineGroup d,
    {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
    {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

/-- Two subgroups `G₁, G₂ ≤ E_d` are **orientation-preserving affinely
equivalent**: conjugation by a positive-determinant affine map takes
one to the other. -/
def AffOPEquivalent {d : ℕ} (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  ∃ φ : AffineGroup d, 0 < (φ.linear.det : ℝ) ∧
    {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
    {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

/-- Count of crystallographic groups modulo affine equivalence. -/
noncomputable def crystallographicCount (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (CrystallographicGroup d) |
    ∃ G₀ : CrystallographicGroup d,
      S = {H : CrystallographicGroup d | AffinelyEquivalent G₀.1 H.1}}

/-- Count of crystallographic groups modulo orientation-preserving
affine equivalence. -/
noncomputable def crystallographicCountOP (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (CrystallographicGroup d) |
    ∃ G₀ : CrystallographicGroup d,
      S = {H : CrystallographicGroup d | AffOPEquivalent G₀.1 H.1}}

/-- Count of orientation-preserving crystallographic groups modulo
orientation-preserving affine equivalence. -/
noncomputable def crystallographicCountOPOnly (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set { G : CrystallographicGroup d //
                          ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g } |
    ∃ G₀ : { G : CrystallographicGroup d //
              ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g },
      S = {H | AffOPEquivalent G₀.1.1 H.1.1}}

end SpaceGroupsProblem
end Geometry
end LeanEval


