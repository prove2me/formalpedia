-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarSurj
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarSurj
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:25.474954+00:00
-- url     : https://prove2.me/theorems/bf9d6046-5f99-5050-8a02-47b9878d17e0
-- title:
--   Statements Cone Var Surj
-- statement:
--   Definitions and structural lemmas for Statements Cone Var Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConeVarSurj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConePolyLocalization
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
def ConeVarSurj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ z : coneLocal P W hPW, ∃ (p q : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ),
      IsUnit (q.coeff e) ∧ z * coneVarMap P W hPW v q = coneVarMap P W hPW v p
end
end GroundTheory.Heights₂.Heights.FieldNumbers


