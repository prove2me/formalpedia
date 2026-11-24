-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivSupport
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:09.369174+00:00
-- url     : https://prove2.me/theorems/fea0918e-a3ce-4f13-aeb2-7a50b7b8910d
-- title:
--   Statements Div Support
-- statement:
--   Definitions and structural lemmas for Statements Div Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDivSupport.lean

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
def DivCycleSupport.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (f : MRing ι F), IsMultiHomog f c → f ∉ P →
    ∀ W : Ideal (MRing ι F), divCycle P f W ≠ 0 → IsMultiProjPrime W ∧ relDim W = (n : ℕ)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


