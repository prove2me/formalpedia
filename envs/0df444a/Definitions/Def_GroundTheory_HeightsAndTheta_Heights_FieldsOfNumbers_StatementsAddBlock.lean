-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:46.053827+00:00
-- url     : https://prove2.me/theorems/49e9ce17-11d4-4ef0-b06d-2e9d25990728
-- title:
--   Statements Add Block
-- statement:
--   Definitions and structural lemmas for Statements Add Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsAddBlock.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
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
def projSpaceHilb (N : ℕ) (t : ℤ) : ℤ :=
  if 0 ≤ t then (((t.toNat + N).choose N : ℕ) : ℤ) else 0
def HilbAddBlock.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (N : ℕ) (m : Option K → ℤ),
    hilbFn (addBlockPrime N I) m = hilbFn I (fun k => m (some k)) * projSpaceHilb N (m none)
example : projSpaceHilb 1 2 = 3 ∧ projSpaceHilb 2 2 = 6 ∧ projSpaceHilb 2 (-1) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
end
end GroundTheory.Heights₂.Heights.FieldNumbers


