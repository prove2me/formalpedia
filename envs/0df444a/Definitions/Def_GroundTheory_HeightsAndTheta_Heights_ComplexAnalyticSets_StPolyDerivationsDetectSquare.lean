-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyDerivationsDetectSquare
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyDerivationsDetectSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:07.927724+00:00
-- url     : https://prove2.me/theorems/408bde04-791a-428d-90eb-744ad3da7799
-- title:
--   St Poly Derivations Detect Square
-- statement:
--   Definitions and structural lemmas for St Poly Derivations Detect Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPolyDerivationsDetectSquare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
def PolyDerivationsDetectSquare.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime]
    (g : MvPolynomial (Fin n) k), g ∈ p →
      (∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) →
        algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
          maximalIdeal (Localization.AtPrime p) ^ 2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


