-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassMono
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:48.266023+00:00
-- url     : https://prove2.me/theorems/1d5fef9c-60a2-47a2-9c90-bac5eba6498e
-- title:
--   St Slice Reg Mass Mono
-- statement:
--   Definitions and structural lemmas for St Slice Reg Mass Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegMassMono.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def SliceRegMassMono.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε : ℝ)
    (a b : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
    Measurable a → Measurable b → (∀ x, 0 ≤ a x) → (∀ x, a x ≤ b x) → (∀ x, b x ≤ 1) →
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a (fun _ x => Real.log (h.dualNorm x)) ≤
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b (fun _ x => Real.log (h.dualNorm x))
end
end GroundTheory.Heights₂.Heights


