-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCMUnmixed
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCMUnmixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:56.100001+00:00
-- url     : https://prove2.me/theorems/d18a109c-bb23-4762-a79d-e94c6d03a04b
-- title:
--   St Slice CMUnmixed
-- statement:
--   Definitions and structural lemmas for St Slice CMUnmixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCMUnmixed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
open MvPolynomial Matrix ComplexSets IsLocalRing
def SliceCMUnmixed.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ),
    IsCohenMacaulayAt J q → ringKrullDim (localRingAt J q) = (d + 1 : ℕ) →
    ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ) →
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
        P ≤ RingHom.ker (eval q) →
          P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)
end GroundTheory.Heights₂.Heights


