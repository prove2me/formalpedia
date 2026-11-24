-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:53.306508+00:00
-- url     : https://prove2.me/theorems/d9a1788f-4a52-4ae7-9119-573846d0cc79
-- title:
--   St Normalisation Model Localization
-- statement:
--   Definitions and structural lemmas for St Normalisation Model Localization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalisationModelLocalization.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
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
def normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ) : Submonoid (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
  (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl.map
    ((Ideal.Quotient.mk M.ideal).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom)
def NormalisationModelLocalization.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime →
      ∃ e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q),
        ∀ f : MvPolynomial (Fin n) ℂ,
          e (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)) =
            algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
              (Ideal.Quotient.mk M.ideal (rename Sum.inl f))
end
end GroundTheory.Heights₂.Heights


