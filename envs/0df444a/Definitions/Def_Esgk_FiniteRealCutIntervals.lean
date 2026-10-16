-- Prove2me | Definitions.Def_Esgk_FiniteRealCutIntervals
-- name    : Esgk_FiniteRealCutIntervals
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:49.811114+00:00
-- url     : https://prove2.me/theorems/87b1cce2-ecfd-4c3d-b6c3-e61e91a5da44
-- title:
--   Intervals cut out by a finite set of real values
-- statement:
--   This assigns to each optional cut point the portion of a real set lying before the first cut or between that cut and the next larger cut.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical

namespace Esgk

 
def realCutInterval (J : Set ℝ) (T : Finset ℝ) : Option {t // t ∈ T} → Set ℝ
  | none => {x | x ∈ J ∧ ∀ t ∈ T, x < t}
  | some c => {x | x ∈ J ∧ (c : ℝ) < x ∧ ∀ t ∈ T, (c : ℝ) < t → x < t}


end Esgk


