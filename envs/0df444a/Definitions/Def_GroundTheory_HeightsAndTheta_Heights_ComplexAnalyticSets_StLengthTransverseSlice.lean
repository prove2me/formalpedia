-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:57.788485+00:00
-- url     : https://prove2.me/theorems/f507f03a-4ac5-40e4-be3a-2dd7b3a91397
-- title:
--   St Length Transverse Slice
-- statement:
--   Definitions and structural lemmas for St Length Transverse Slice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthTransverseSlice.lean

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
open MvPolynomial Matrix ComplexSets
noncomputable section
def LengthTransverseSlice.Statement : Prop :=
  ∀ (n d : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ),
    W ∈ I.minimalPrimes → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → q ∈ zeroSet W →
    (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) → IsCohenMacaulayAt I q →
    IsTransverseSliceAt W L q →
      localMult I W = localMult (sliceIdeal I L q) (RingHom.ker (eval q))
end
end GroundTheory.Heights₂.Heights


