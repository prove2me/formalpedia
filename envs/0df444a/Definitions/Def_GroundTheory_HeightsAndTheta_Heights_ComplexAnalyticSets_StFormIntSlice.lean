-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormIntSlice
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormIntSlice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:47.164182+00:00
-- url     : https://prove2.me/theorems/8d7cc141-5b6f-4c97-95cb-d0c4af81d9fc
-- title:
--   St Form Int Slice
-- statement:
--   Definitions and structural lemmas for St Form Int Slice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFormIntSlice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
variable {n : ℕ}
def FormIntSlice.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (a b : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContinuousOn a {x | x ≠ 0} →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → b (t • x) = b x) → ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      formInt h W e a b =
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons b fun _ x => Real.log (h.dualNorm x))
end
end GroundTheory.Heights₂.Heights


