-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConePolyLocalization
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConePolyLocalization
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:18.742079+00:00
-- url     : https://prove2.me/theorems/2debeaf2-2901-5711-a2d9-358f420dd8c8
-- title:
--   Statements Cone Poly Localization
-- statement:
--   Definitions and structural lemmas for Statements Cone Poly Localization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConePolyLocalization.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
theorem isPrime_map_C_mvPolynomial {A : Type*} [CommRing A] (σ : Type*) (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _
section Cone
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
def coneVarMap (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (v : ∀ k, ι k) :
    MvPolynomial K (degZeroLoc P {W}) →ₐ[degZeroLoc P {W}] coneLocal P W hPW :=
  aeval fun k => algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩))
end Cone
def ConePolyLocalization.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})),
      letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
      haveI := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
      IsLocalization.AtPrime (coneLocal P W hPW)
        ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
end
end GroundTheory.Heights₂.Heights.FieldNumbers


