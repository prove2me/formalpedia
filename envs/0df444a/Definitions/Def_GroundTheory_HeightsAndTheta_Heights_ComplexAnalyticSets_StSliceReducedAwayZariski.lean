-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:36.643715+00:00
-- url     : https://prove2.me/theorems/5bdfc7c6-5dbe-4d73-ab3f-88c4f658a122
-- title:
--   St Slice Reduced Away Zariski
-- statement:
--   Definitions and structural lemmas for St Slice Reduced Away Zariski, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceReducedAwayZariski.lean

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
open MvPolynomial Matrix
noncomputable section
def SliceReducedAwayZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
      ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
        ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
          P ≠ RingHom.ker (eval q) →
            ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q
end
end GroundTheory.Heights₂.Heights


