-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarNumerator
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarNumerator
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:33:04.679199+00:00
-- url     : https://prove2.me/theorems/2d2fa8e2-850e-5e50-bbff-bbe98eaa44c5
-- title:
--   Statements Cone Var Numerator
-- statement:
--   Definitions and structural lemmas for Statements Cone Var Numerator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConeVarNumerator.lean

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
def ConeVarNumerator.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ p : MvPolynomial K (degZeroLoc P {W}),
      ∃ (b : K → ℕ) (g : MRing ι F) (h : (K →₀ ℕ) → MRing ι F),
        IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (h d) b) ∧
        (∀ d, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (h d)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)) ∧
        ((coneVarMap P W hPW v p : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
              (Ideal.Quotient.mk P (∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


