-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegVarBound
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegVarBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:23.046685+00:00
-- url     : https://prove2.me/theorems/870f3c1a-fbd2-4ba7-aad1-9fa82bb78f2a
-- title:
--   St Slice Reg Var Bound
-- statement:
--   Definitions and structural lemmas for St Slice Reg Var Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegVarBound.lean

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
def SliceRegVarBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε C : ℝ)
    (b₁ b₂ w : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
    Measurable b₁ → Measurable b₂ → Measurable w →
    (∀ x, |b₁ x| ≤ C) → (∀ x, |b₂ x| ≤ C) → (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x, |b₁ x - b₂ x| ≤ C * w x) →
      |varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b₁
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b₂
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))| ≤
        C * (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
          2 * varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
            (fun _ x => Real.log (h.dualNorm x)))
end
end GroundTheory.Heights₂.Heights


