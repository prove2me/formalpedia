-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreDimGe
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreDimGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:54.784716+00:00
-- url     : https://prove2.me/theorems/fc87a3c0-72af-42df-b29f-d019d14d224f
-- title:
--   Statements Segre Dim Ge
-- statement:
--   Definitions and structural lemmas for Statements Segre Dim Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSegreDimGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
def SegreDimGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ((e + 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


