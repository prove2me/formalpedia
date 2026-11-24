-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceFormLelong
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceFormLelong
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:48:09.634215+00:00
-- url     : https://prove2.me/theorems/e8ff2ccb-658f-468f-9cc2-17f6134b4116
-- title:
--   St Slice Form Lelong
-- statement:
--   Definitions and structural lemmas for St Slice Form Lelong, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceFormLelong.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormIntSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
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
def SliceFormLelong.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContDiffOn ℝ ∞ a {x | x ≠ 0} →
      Tendsto (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (𝓝[>] 0)
        (𝓝 (∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
            varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e a (fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a (fun _ x => Real.log (h.dualNorm x))))
end
end GroundTheory.Heights₂.Heights


