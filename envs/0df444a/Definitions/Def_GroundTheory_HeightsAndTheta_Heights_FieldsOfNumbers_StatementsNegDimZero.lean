-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNegDimZero
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNegDimZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:52.68296+00:00
-- url     : https://prove2.me/theorems/1338d971-ed99-48c6-92be-c33c580b943a
-- title:
--   Statements Neg Dim Zero
-- statement:
--   Definitions and structural lemmas for Statements Neg Dim Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsNegDimZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
def HilbNegDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    relDim I < 0 → ∀ᶠ m in Filter.atTop, hilbFn I m = 0
abbrev pointCoord : Σ _ : Unit, ProjIdx 0 () := ⟨(), 0⟩
def pointSquareIdeal (F : Type*) [Field F] : Ideal (MRing (ProjIdx 0) F) :=
  Ideal.span ((fun s => monomial s (1 : F)) '' {Finsupp.single pointCoord 2})
end
end GroundTheory.Heights₂.Heights.FieldNumbers


