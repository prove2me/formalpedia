-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
-- name    : ProbabilityTheory_chapter_01_thm_1_1_basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:51:37.888204+00:00
-- url     : https://prove2.me/theorems/44476ee0-85fd-4ee6-87d3-4c2aae35fec4
-- title:
--   Chapter 1, thm_1_1_basic: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_basic`: `discontinuitySetOn`, `continuousWithinAt_of_not_mem_discontinuitySetOn`, `strict_interval_of_rsIntegrable`, `not_rsIntegrable_refl`, `discontinuitySetOn_const_refl_empty`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open Finset BigOperators
open Set Topology

noncomputable section

def discontinuitySetOn (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x}
namespace Thm11SourceRoute

lemma continuousWithinAt_of_not_mem_discontinuitySetOn {f : ℝ → ℝ} {a b x : ℝ}
    (hxI : x ∈ Icc a b) (hx : x ∉ discontinuitySetOn f a b) :
    ContinuousWithinAt f (Icc a b) x := by
  by_contra hcont
  exact hx ⟨hxI, hcont⟩

lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨w⟩
  exact w.source_limit.1.1

lemma not_rsIntegrable_refl (f α : ℝ → ℝ) (a : ℝ) :
    ¬ RSIntegrable f α a a := by
  intro h
  exact (lt_irrefl a) (strict_interval_of_rsIntegrable h)

lemma discontinuitySetOn_const_refl_empty (c a : ℝ) :
    discontinuitySetOn (fun _ : ℝ => c) a a = ∅ := by
  ext x
  constructor
  · intro hx
    exact hx.2 (by
      simpa using
        (continuousAt_const.continuousWithinAt :
          ContinuousWithinAt (fun _ : ℝ => c) (Icc a a) x))
  · intro hx
    cases hx
end Thm11SourceRoute


