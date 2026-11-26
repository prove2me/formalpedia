-- Prove2me | Definitions.Def_Spectral_PVM_Basic
-- name    : Spectral_PVM_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:52:05.623599+00:00
-- url     : https://prove2.me/theorems/685104db-1da5-4dc5-a4b2-8e3c62276ca6
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
structure PVM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  proj : Set ℝ → (E →L[ℂ] E)
  isOrthogonalProjection : ∀ S, MeasurableSet S →
    IsSelfAdjoint (proj S) ∧ IsIdempotentElem (proj S)
  empty : proj ∅ = 0
  univ : proj Set.univ = 1
  inter : ∀ S T, MeasurableSet S → MeasurableSet T →
    proj (S ∩ T) = proj S * proj T
  countably_additive : ∀ (S : ℕ → Set ℝ),
    (∀ i, MeasurableSet (S i)) →
    Pairwise (Disjoint on S) →
    ∀ x, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, proj (S i) x)
      Filter.atTop (nhds (proj (⋃ i, S i) x))


