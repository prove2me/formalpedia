-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceUnmixedGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceUnmixedGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:57.614816+00:00
-- url     : https://prove2.me/theorems/59e70392-91ea-4598-997d-3756618a18ea
-- title:
--   St Slice Unmixed General
-- statement:
--   Definitions and structural lemmas for St Slice Unmixed General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceUnmixedGeneral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedGeneral
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
def SliceUnmixedGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ)
              (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
            P ≤ RingHom.ker (eval q) →
              P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)
end
end GroundTheory.Heights₂.Heights


