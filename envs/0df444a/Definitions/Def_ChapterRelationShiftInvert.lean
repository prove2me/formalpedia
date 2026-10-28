-- Prove2me | Definitions.Def_ChapterRelationShiftInvert
-- name    : ChapterRelationShiftInvert
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T14:29:56.020181+00:00
-- url     : https://prove2.me/theorems/0b24287d-b025-46de-8d22-4c02bc84b321
-- title:
--   Chapter RelationShiftInvert
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterRelationShiftInvert.lean`): generated def bundle for ChapterRelationShiftInvert. See BookProof/ChapterRelationShiftInvert.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterRelationShiftInvert.lean

import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterPositiveSquareRootUnique
import Mathlib


/-!
# The resolvent of a non-negative self-adjoint relation is its Hashimoto shift-invert

`BookProof.ChapterNonnegSquareRoot` built, for a non-negative self-adjoint linear
relation `T` and every `γ > 0`, the everywhere-defined bounded resolvent
`(T + γ)⁻¹ = invCLMAt hT hγ`, and `BookProof.ChapterNonnegUnitaryGroup` built from it the
unitary group `e^{-itT}`.  `BookProof.ChapterHashimotoShiftInvert` describes the operator
the Hashimoto/SIRK shift-invert rational-Krylov algorithm actually applies to a *densely
defined operator* `A : Dom →ₗ[ℂ] F`: the shift-invert `R = (A + γ)⁻¹`, characterized by
the predicate `IsShiftInvert A γ R`.  This chapter is the bridge between the two.

* `relDomain T` is the domain of the relation and `mem_relDomain_iff` describes it;
  `snd_unique` is single-valuedness, and **`relOp hsv`** is the *operator part* of a
  single-valued relation — the honest linear map `relDomain T →ₗ[ℂ] F` whose graph is `T`
  (`relOp_mem`).
* **`isShiftInvert_invCLMAt`**: for every `γ > 0` the resolvent `(T + γ)⁻¹` **is** the
  Hashimoto shift-invert of `relOp hsv` at the shift `γ`.  So the whole shift-invert layer
  — the norm bound `‖R‖ ≤ 1/γ`, the Galerkin convergence theory, and the selection
  theorems — applies verbatim to the resolvent family of this thread.
* The unitary group of the previous chapter is therefore the dynamics of the operator the
  algorithm selects: its orbits stay in the domain (`unitaryU_mem_relDomain`), it commutes
  with the operator part (`relOp_unitaryU`), and it solves the Schrödinger equation
  `d/dt (e^{-itT} x) = -i e^{-itT} (T x)` there (`hasDerivAt_unitaryU_relOp`).
* **`unitaryU_eq_of_invCLM_eq`**: the shift-invert operator at a single shift already
  determines the unitary group — two non-negative self-adjoint relations with the same
  shift-invert generate the same `e^{-itT}`.

## Honest boundary

Nothing here is claimed about any particular physical Hamiltonian: this is the interface
statement that the resolvent family of a non-negative self-adjoint relation is exactly the
input the Hashimoto/SIRK layer consumes, and that the dynamics it determines is a unitary
group.
-/

namespace BookProof.RelationShiftInvert

open BookProof.PositiveSquareRoot BookProof.NonnegSquareRoot BookProof.NonnegResolvent
open BookProof.NonnegUnitaryGroup BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

/-- The **domain** of a linear relation. -/
def relDomain (T : Submodule ℂ (F × F)) : Submodule ℂ F := T.map (LinearMap.fst ℂ F F)

omit [CompleteSpace F] in
theorem mem_relDomain_iff {x : F} : x ∈ relDomain T ↔ ∃ k : F, (x, k) ∈ T := by
  constructor
  · intro hx
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hx
    refine ⟨p.2, ?_⟩
    have hpe : p = (x, p.2) := by
      rw [← hp1]
      simp
    rwa [← hpe]
  · rintro ⟨k, hk⟩
    exact Submodule.mem_map.2 ⟨(x, k), hk, rfl⟩

omit [CompleteSpace F] in
/-- The value of a single-valued relation is unique. -/
theorem snd_unique (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {x k₁ k₂ : F}
    (h₁ : (x, k₁) ∈ T) (h₂ : (x, k₂) ∈ T) : k₁ = k₂ := by
  have hsub : ((0 : F), k₁ - k₂) ∈ T := by
    have := T.sub_mem h₁ h₂
    simpa using this
  exact sub_eq_zero.1 (hsv _ hsub)

/-- The value of the relation at a point of its domain. -/
noncomputable def relOpFun (x : relDomain T) : F :=
  Classical.choose (mem_relDomain_iff.1 x.2)

omit [CompleteSpace F] in
theorem relOpFun_mem (x : relDomain T) : ((x : F), relOpFun x) ∈ T :=
  Classical.choose_spec (mem_relDomain_iff.1 x.2)

omit [CompleteSpace F] in
theorem relOpFun_eq (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {x : relDomain T} {k : F}
    (h : ((x : F), k) ∈ T) : relOpFun x = k :=
  snd_unique hsv (relOpFun_mem x) h

/-- **The operator part of a single-valued linear relation.** -/
noncomputable def relOp (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) : relDomain T →ₗ[ℂ] F where
  toFun x := relOpFun x
  map_add' x y := by
    refine relOpFun_eq hsv ?_
    have h := T.add_mem (relOpFun_mem x) (relOpFun_mem y)
    simpa using h
  map_smul' c x := by
    refine relOpFun_eq hsv ?_
    have h := T.smul_mem c (relOpFun_mem x)
    simpa using h







/-! ## The unitary group of the selected operator -/







end BookProof.RelationShiftInvert


