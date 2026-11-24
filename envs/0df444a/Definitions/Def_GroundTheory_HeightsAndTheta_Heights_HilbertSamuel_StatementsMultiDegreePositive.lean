-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:29.845225+00:00
-- url     : https://prove2.me/theorems/07f76ab3-0ea2-4bf2-b09d-2f8ef8bb1a99
-- title:
--   Statements Multi Degree Positive
-- statement:
--   Definitions and structural lemmas for Statements Multi Degree Positive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsMultiDegreePositive.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegreePositive
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
def MultiDegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ))
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


