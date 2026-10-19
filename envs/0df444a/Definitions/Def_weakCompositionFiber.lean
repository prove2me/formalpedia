-- Prove2me | Definitions.Def_weakCompositionFiber
-- name    : weakCompositionFiber
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T18:52:47.119987+00:00
-- url     : https://prove2.me/theorems/e11dfda1-4d6d-419f-86a7-1d4b631b04da
-- title:
--   Finite weak-composition fiber
-- statement:
--   The subtype of functions α → Fin (k + 1) whose natural values sum to k, in the same universe as α.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

open scoped BigOperators

universe u

namespace OAI.PiExponent.LiteralAnalytic

/-- Bounded functions whose values form a weak composition of k. -/
abbrev weakCompositionFiber (α : Type u) [Fintype α] (k : ℕ) : Type u :=
  { f : α → Fin (k + 1) // Finset.univ.sum (fun a => (f a).val) = k }

end OAI.PiExponent.LiteralAnalytic


