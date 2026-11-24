-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:25.338511+00:00
-- url     : https://prove2.me/theorems/d7d5533b-d557-43e4-a798-1878e3fdc224
-- title:
--   St Slice Mult General
-- statement:
--   Definitions and structural lemmas for St Slice Mult General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceMultGeneral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
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
def SliceMultGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, localMult (J ⊔ Ideal.span {linForm u}) W =
            localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))
end
end GroundTheory.Heights₂.Heights


