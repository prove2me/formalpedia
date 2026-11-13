-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:54:12.531854+00:00
-- url     : https://prove2.me/theorems/2068688d-1e66-4bf5-b050-ccd319d2ebb0
-- title:
--   Chapter 1, thm_1_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_3`: `sourceHypotheses_integrator_add`, `upperSum_integrator_add`, `lowerSum_integrator_add`, `taggedSum_integrator_add`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise
open Finset
open Set

noncomputable section

section Thm_1_3_helper

theorem sourceHypotheses_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    (h₁ : SourceHypotheses a b f α₁)
    (h₂ : SourceHypotheses a b f α₂) :
    SourceHypotheses a b f (fun x => α₁ x + α₂ x) := by
  rcases h₁ with ⟨hab, hAbove, hBelow, hmono₁⟩
  rcases h₂ with ⟨_hab₂, _hAbove₂, _hBelow₂, hmono₂⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  exact add_le_add (hmono₁ hx hy hxy) (hmono₂ hx hy hxy)

theorem upperSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    upperSum P f (fun x => α₁ x + α₂ x) =
      upperSum P f α₁ + upperSum P f α₂ := by
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem lowerSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    lowerSum P f (fun x => α₁ x + α₂ x) =
      lowerSum P f α₁ + lowerSum P f α₂ := by
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem taggedSum_integrator_add {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f α₁ α₂ : ℝ → ℝ) :
    taggedSum P tags f (fun x => α₁ x + α₂ x) =
      taggedSum P tags f α₁ + taggedSum P tags f α₂ := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

end Thm_1_3_helper

section Theorem_1_3

end Theorem_1_3

section integrator_scalar_multiply

end integrator_scalar_multiply


