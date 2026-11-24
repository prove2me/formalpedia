-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIndependentModBaseChange
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIndependentModBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:55.643044+00:00
-- url     : https://prove2.me/theorems/df972673-a1ce-4872-8b18-fd559156d8bc
-- title:
--   Statements Independent Mod Base Change
-- statement:
--   Definitions and structural lemmas for Statements Independent Mod Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsIndependentModBaseChange.lean

import Mathlib
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
open MvPolynomial
noncomputable section
def IndependentModBaseChange.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℤ)) (r : ℕ) (g : Fin r → MvPolynomial σ ℤ),
    LinearIndependent ℤ (fun i => Ideal.Quotient.mk P (g i)) →
    LinearIndependent ℂ (fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i)))
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


