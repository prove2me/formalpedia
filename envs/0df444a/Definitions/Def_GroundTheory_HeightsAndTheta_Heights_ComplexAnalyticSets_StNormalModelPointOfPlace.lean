-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPointOfPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPointOfPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:54.966992+00:00
-- url     : https://prove2.me/theorems/46955932-ccba-429c-9f63-451b121e3c15
-- title:
--   St Normal Model Point Of Place
-- statement:
--   Definitions and structural lemmas for St Normal Model Point Of Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPointOfPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimePlaceBranchExists
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
def NormalModelPointOfPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ∀ P : MaximalSpectrum (curveNormalisation J q),
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
            Ring.ord (pointLocalRing M.ideal w)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))
end
end GroundTheory.Heights₂.Heights


