-- Prove2me | Definitions.Def_Esgk_FiniteIncidenceCodegreeBound
-- name    : Esgk_FiniteIncidenceCodegreeBound
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:49.752283+00:00
-- url     : https://prove2.me/theorems/86eebc29-6bd7-4b57-83d7-e5e2d5e9d4b6
-- title:
--   Counting finite incidences by target labels
-- statement:
--   This counts pairs in finite source and target sets satisfying a given relation by summing the filtered source cardinalities over target labels.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

def finiteIncidenceCount {α β : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop) : ℕ := by
  classical
  exact ∑ b ∈ C, (P.filter (fun x ↦ R x b)).card


end Esgk


