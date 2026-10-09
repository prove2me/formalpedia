-- Prove2me | Definitions.Def_OAIErdos3B092
-- name    : OAIErdos3B092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T14:08:01.224882+00:00
-- url     : https://prove2.me/theorems/3d6bbea4-f306-4bdc-9c98-5a4372ced122
-- title:
--   OpenAI Erdős-3 split, definitions bundle 93 of 93
-- statement:
--   Definitions bundle 93 of 93 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B091`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 93 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieBCHGroup.realification_grid_iff`, `OAI.Erdos3.realDenominatorGrid_exists_rational`, `OAI.Erdos3.real_grid_exists_rationalLieInclusion`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B018

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealGridRationalLift
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_exists_rational {ι : Type*} (l : ℕ) (hl : 0 < l)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ∃ y : ι → ℚ, y ∈ denominatorGrid l ∧ (fun i => (y i : ℝ)) = x := by
  obtain ⟨z, hz⟩ := hx
  let y : ι → ℚ := fun i => (z i : ℚ) / l
  have hy : (fun i => (y i : ℝ)) = x := by
    funext i
    change (((z i : ℚ) / l : ℚ) : ℝ) = x i
    push_cast
    apply (div_eq_iff (show (l : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hl.ne')).mpr
    have hi := congrFun hz i
    change (z i : ℝ) = (l : ℝ) * x i at hi
    simpa only [mul_comm] using hi
  refine ⟨y, (real_cast_mem_denominatorGrid_iff l y).mp ?_, hy⟩
  rw [hy]
  exact ⟨z, hz⟩

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_grid_exists_rationalLieInclusion (e : Basis ι ℚ L) (l : ℕ) (hl : 0 < l)
    (x : ℝ ⊗[ℚ] L) (hx : (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    ∃ a : L, e.equivFun a ∈ denominatorGrid l ∧ rationalLieInclusion a = x := by
  obtain ⟨y, hy, heq⟩ := realDenominatorGrid_exists_rational l hl _ hx
  refine ⟨e.equivFun.symm y, ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hy
  · apply (e.baseChange ℝ).equivFun.injective
    funext i
    calc
      _ = (e.equivFun (e.equivFun.symm y) i : ℝ) :=
        rationalLieInclusion_coordinates e (e.equivFun.symm y) i
      _ = (y i : ℝ) := by rw [LinearEquiv.apply_symm_apply]
      _ = _ := congrFun heq i

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_grid_iff (e : Basis ι ℚ L) (l : ℕ) (hl : 0 < l)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l ↔
      ∃ a : NilpotentLieBCHGroup L s hnil,
        e.equivFun a.coord ∈ denominatorGrid l ∧ realificationHom a = g := by
  constructor
  · intro hg
    obtain ⟨a, ha, heq⟩ := real_grid_exists_rationalLieInclusion e l hl g.coord hg
    exact ⟨⟨a⟩, ha, ext heq⟩
  · rintro ⟨a, ha, rfl⟩
    rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
    exact ha

end NilpotentLieBCHGroup
end Erdos3

end

end OAI

end


