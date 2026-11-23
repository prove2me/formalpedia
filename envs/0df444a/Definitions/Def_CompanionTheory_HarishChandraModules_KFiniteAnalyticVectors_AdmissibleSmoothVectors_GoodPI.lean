-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:14.851087+00:00
-- url     : https://prove2.me/theorems/b3812c27-f507-40c0-bf0d-49fa08231751
-- title:
--   Good PI
-- statement:
--   Definitions and structural lemmas for Good PI, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace CompanionTheory.D.gk.admitted
section Lin
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def perp (T : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {y | ∀ x ∈ T, star y ⬝ᵥ x = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [star_add, add_dotProduct, ha x hx, hb x hx, add_zero]
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro c a ha x hx
    rw [star_smul, smul_dotProduct, ha x hx, smul_zero]
end Lin
end CompanionTheory.D.gk.admitted


