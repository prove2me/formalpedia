-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:03.524349+00:00
-- url     : https://prove2.me/theorems/36e6b421-bd80-4ca0-9d46-89823cb56791
-- title:
--   St Slice Local Dim General
-- statement:
--   Definitions and structural lemmas for St Slice Local Dim General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceLocalDimGeneral.lean

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
def SliceLocalDimGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
        ∀ L ∈ O, ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ)
end GroundTheory.Heights₂.Heights


