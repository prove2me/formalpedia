-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTail
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:56.42436+00:00
-- url     : https://prove2.me/theorems/01426bc8-10f0-4c92-9485-10df614f3373
-- title:
--   St Slice Reg Tail
-- statement:
--   Definitions and structural lemmas for St Slice Reg Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceFormLelong
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
def SliceRegTail.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContinuousOn a {x | x ≠ 0} →
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k → ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        |varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => sliceCut h k x * a x)
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))| ≤ δ
end
end GroundTheory.Heights₂.Heights


