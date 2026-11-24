-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StModelLocalizationMaximalPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StModelLocalizationMaximalPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:08.612102+00:00
-- url     : https://prove2.me/theorems/ae4bfaaa-4dbe-40eb-867e-3977c74fd7ff
-- title:
--   St Model Localization Maximal Point
-- statement:
--   Definitions and structural lemmas for St Model Localization Maximal Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StModelLocalizationMaximalPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
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
def ModelLocalizationMaximalPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (P : Ideal (Localization (normalModelSubmonoid M q))), P.IsMaximal →
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        P.comap ((algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))).comp
            (Ideal.Quotient.mk M.ideal)) =
          RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)
end
end GroundTheory.Heights₂.Heights


