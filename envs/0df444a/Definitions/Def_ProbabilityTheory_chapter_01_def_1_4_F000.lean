-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_4_F000
-- name    : ProbabilityTheory_chapter_01_def_1_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:43:07.574007+00:00
-- url     : https://prove2.me/theorems/76fa31f8-6289-401c-9d1c-2dba351b39eb
-- title:
--   Chapter 1, def_1_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `def_1_4`: `improperRSFilter`, `rsTruncIntegral`, `ImproperRSConvergesTo`, `ImproperRSIntegrable`, `improperRSIntegral`, and 2 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open Filter

noncomputable section

def improperRSFilter : Filter (ℝ × ℝ) :=
  (atBot ×ˢ atTop) ⊓ Filter.principal {p : ℝ × ℝ | p.1 ≤ p.2}

noncomputable def rsTruncIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  by
    classical
    exact if h : RSIntegrable f α a b then rsIntegral f α a b h else 0

def ImproperRSConvergesTo (f α : ℝ → ℝ) (I : ℝ) : Prop :=
  (∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable f α p.1 p.2) ∧
    Tendsto
      (fun p : ℝ × ℝ => rsTruncIntegral f α p.1 p.2)
      improperRSFilter
      (nhds I)

def ImproperRSIntegrable (f α : ℝ → ℝ) : Prop :=
  ∃ I : ℝ, ImproperRSConvergesTo f α I

noncomputable def improperRSIntegral
  (f α : ℝ → ℝ) (h : ImproperRSIntegrable f α) : ℝ :=
  Classical.choose h

theorem improperRSIntegral_spec {f α : ℝ → ℝ} (h : ImproperRSIntegrable f α) :
    ImproperRSConvergesTo f α (improperRSIntegral f α h) :=
  Classical.choose_spec h

def def_1_4 (f α : ℝ → ℝ) : Prop :=
  ImproperRSIntegrable f α


