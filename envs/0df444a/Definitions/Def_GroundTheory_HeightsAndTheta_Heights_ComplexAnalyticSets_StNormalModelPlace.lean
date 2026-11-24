-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:39.790963+00:00
-- url     : https://prove2.me/theorems/b67d6840-3a8d-4417-acd3-077ceca72dea
-- title:
--   St Normal Model Place
-- statement:
--   Definitions and structural lemmas for St Normal Model Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
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
open MvPolynomial
noncomputable section
variable {σ : Type*}
instance isPrime_ker_eval_point (w : σ → ℂ) : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _
def pointLocalRing (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Type _ :=
  Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))
instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : CommRing (pointLocalRing I w) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))
instance (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Algebra (MvPolynomial σ ℂ) (pointLocalRing I w) :=
  inferInstanceAs (Algebra (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ⧸
    I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))
def NormalModelPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal → IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
          Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))
end
end GroundTheory.Heights₂.Heights


