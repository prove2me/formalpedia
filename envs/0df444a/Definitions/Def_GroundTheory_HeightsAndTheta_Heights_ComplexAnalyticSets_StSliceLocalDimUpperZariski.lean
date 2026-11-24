-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:38.558691+00:00
-- url     : https://prove2.me/theorems/10d3a40f-51e1-4d1e-9f87-5bdca5af638f
-- title:
--   St Slice Local Dim Upper Zariski
-- statement:
--   Definitions and structural lemmas for St Slice Local Dim Upper Zariski, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceLocalDimUpperZariski.lean

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
def SliceLocalDimUpperZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
        ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
          ringKrullDim (localRingAt (sliceIdeal J L q) q) ≤ (1 : ℕ)
end
end GroundTheory.Heights₂.Heights


