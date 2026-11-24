-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:26.349696+00:00
-- url     : https://prove2.me/theorems/415fa6ac-8089-4955-97d4-937c99d72768
-- title:
--   St Slice Length
-- statement:
--   Definitions and structural lemmas for St Slice Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceLength.lean

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
open MvPolynomial Matrix ComplexSets
noncomputable section
def SliceLength.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet W ⊆ closure (zeroSet W ∩ U) ∧
        ∀ q ∈ zeroSet W ∩ U, Dense {L : Matrix (Fin d) (Fin n) ℂ |
          IsRadicalAt (sliceIdeal J L q) q ∧
            localMult (J ⊔ Ideal.span {linForm u}) W =
              localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))}
end
end GroundTheory.Heights₂.Heights


