-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:30.559581+00:00
-- url     : https://prove2.me/theorems/ffd5d8cd-51e6-4704-a207-968d500f5fd8
-- title:
--   St Transverse Slice General
-- statement:
--   Definitions and structural lemmas for St Transverse Slice General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseSliceGeneral.lean

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
def TransverseSliceGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        IsOpen {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} ∧
          Dense {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q}
end GroundTheory.Heights₂.Heights


