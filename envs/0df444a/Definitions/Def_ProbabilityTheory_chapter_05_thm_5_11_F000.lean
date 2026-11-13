-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_thm_5_11_F000
-- name    : ProbabilityTheory_chapter_05_thm_5_11_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:01:38.256457+00:00
-- url     : https://prove2.me/theorems/5f3bd1d0-80eb-479c-a3cc-ce7372b3c4fe
-- title:
--   Chapter 5, thm_5_11: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `thm_5_11`: `tailSigmaAlgebra`, `thm_5_11`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_11.lean

import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Tactic

open Filter

@[reducible]
def tailSigmaAlgebra {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  limsup (fun n => MeasurableSpace.comap (X n) ‹MeasurableSpace β›) atTop


