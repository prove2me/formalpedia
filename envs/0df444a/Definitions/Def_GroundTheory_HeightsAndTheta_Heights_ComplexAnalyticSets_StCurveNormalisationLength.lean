-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:12.864619+00:00
-- url     : https://prove2.me/theorems/04e047f1-f44c-401d-a853-3b500eb00bb2
-- title:
--   St Curve Normalisation Length
-- statement:
--   Definitions and structural lemmas for St Curve Normalisation Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
instance isPrime_ker_eval (q : Fin n → ℂ) : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _
def curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : CommRing (curveLocalRing I q) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : IsNoetherianRing (curveLocalRing I q) :=
  inferInstanceAs (IsNoetherianRing (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
def curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q)))
instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : CommRing (curveNormalisation I q) :=
  inferInstanceAs (CommRing ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs
    (Algebra (curveLocalRing I q) ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
def curveLocalRingLineEquiv :
    curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0 ≃+*
      Localization.AtPrime (RingHom.ker (eval (0 : Fin 1 → ℂ))) :=
  (Ideal.quotEquivOfEq (Ideal.map_bot)).trans (RingEquiv.quotientBot _)
def CurveNormalisationLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q) →
      (localMult (I ⊔ Ideal.span {f}) (RingHom.ker (eval q)) : ℕ∞) =
        ∑ᶠ P : MaximalSpectrum (curveNormalisation I q),
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) *
            Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ P.asIdeal)
end
end GroundTheory.Heights₂.Heights


