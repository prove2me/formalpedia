-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:02:13.072992+00:00
-- url     : https://prove2.me/theorems/ca4774db-caa3-409f-814f-10a0e628838b
-- title:
--   Statements Div Push Forward Local
-- statement:
--   Definitions and structural lemmas for Statements Div Push Forward Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDivPushForwardLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRelevantPrimeDimGe
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
def DivPushForwardLocal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : MRing (fun k => ι' (j k)) F), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    ∀ M : Ideal (MRing ι' F) → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      cycEval M (divCycle P' (rename (blockIncl j ι') a)) =
        relDeg j P' * divCycle (contractPrime j P') a W
section Example
abbrev LineRing : Type :=
  MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ
abbrev linePointIdeal : Ideal LineRing := Ideal.span {X ⟨(), (0 : Fin 2)⟩}
end Example
end
end GroundTheory.Heights₂.Heights.FieldNumbers


