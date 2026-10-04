-- Prove2me | Definitions.Def_ChapterGroupAverageEsa
-- name    : ChapterGroupAverageEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:41:08.116497+00:00
-- url     : https://prove2.me/theorems/8c903fab-cf16-4fd4-9b39-05b6cfc856e7
-- title:
--   The Lean 4 theorem `mul_eq_one_of_ne_one` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGroupAverageEsa.lean`): generated def bundle for ChapterGroupAverageEsa. See BookProof/ChapterGroupAverageEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterA4
import Mathlib


/-!
# Averaging over a finite group of symmetries: the invariant sector

`BookProof.ReducedEsa` reduces an operator to the range of a single reducing projection, and
treats the two sectors of one self-inverse isometry.  The symmetric (bosonic) and
antisymmetric (fermionic) sectors of an `n`-particle space are the ranges of the *averages*
of a whole finite group of unitaries — the symmetric group acting by permutation of the
factors, possibly twisted by the sign character.  This module supplies the corresponding
instrument in general:

> **Group averaging.**  Let a finite group `G` act on a complex inner product space `F` by
> inner-product-preserving linear maps (a `UnitaryRep`).  Then the average
> `P = |G|⁻¹ Σ_g ρ(g)` is a reducing projection in the sense of
> `BookProof.ReducedEsa.IsReducingProjection`, its range is exactly the joint fixed space of
> the action, and if every `ρ(g)` preserves the domain of an operator `T` and commutes with
> it, then `T` is essentially self-adjoint on the invariant sector as soon as it is
> essentially self-adjoint on its domain.

## Contents

* `UnitaryRep` — a finite-group action by inner-product-preserving linear maps.
* `avgProj` — the average `|G|⁻¹ Σ_g ρ(g)`; `avgProj_apply_of_invariant`,
  `avgProj_smul_invariant` (the average is itself invariant), `mem_range_avgProj_iff` (the
  range is the joint fixed space).
* `isReducingProjection_avgProj` — the average is idempotent and symmetric.
* `commutes_avgProj` — it commutes with any operator each `ρ(g)` commutes with.
* **`essentiallySelfAdjointOn_invariantSector`** — essential self-adjointness on the
  invariant sector, and `symmetricOn_invariantSector` for the symmetry.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.GroupAverage


noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

/-- A finite group acting on an inner product space by inner-product-preserving linear maps.
Unitarity is stated as preservation of the inner product, which for an invertible map is the
same thing; invertibility comes from the group law. -/
structure UnitaryRep (G : Type*) [Group G] (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] where
  /-- the operator attached to a group element -/
  act : G → (F →ₗ[ℂ] F)
  /-- the unit acts as the identity -/
  act_one : ∀ x, act 1 x = x
  /-- the action is multiplicative -/
  act_mul : ∀ g h x, act (g * h) x = act g (act h x)
  /-- every operator of the action preserves the inner product -/
  act_inner : ∀ g x y, (inner ℂ (act g x) (act g y) : ℂ) = inner ℂ x y

namespace UnitaryRep

variable (rep : UnitaryRep G F)





/-- The **average** `|G|⁻¹ Σ_g ρ(g)` of the action. -/
def avgProj : F →ₗ[ℂ] F := ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g













variable {D : Submodule ℂ F}



variable {T : D →ₗ[ℂ] F}







end UnitaryRep

/-! ## The two-element group: the average is the symmetrizing projection -/

/-- In the two-element group, the product of two non-units is the unit. -/
theorem mul_eq_one_of_ne_one : ∀ g h : Multiplicative (ZMod 2), g ≠ 1 → h ≠ 1 → g * h = 1 := by
  decide



/-- A self-inverse isometry is a unitary action of the two-element group. -/
def repOfInvolution (U : F →ₗ[ℂ] F) (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    UnitaryRep (Multiplicative (ZMod 2)) F where
  act g := if g = 1 then LinearMap.id else U
  act_one x := by simp
  act_mul g h x := by
    by_cases hg : g = 1
    · subst hg; simp
    · by_cases hh : h = 1
      · subst hh; simp
      · rw [if_neg hg, if_neg hh, if_pos (mul_eq_one_of_ne_one g h hg hh)]
        simp [hU2]
  act_inner g x y := by
    by_cases h : g = 1 <;> simp [h, hUi]



end

end BookProof.GroupAverage


