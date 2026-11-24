-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetFormCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetFormCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.860751+00:00
-- url     : https://prove2.me/theorems/b5f28c1a-5ac9-4f25-8532-34e5fa41174e
-- title:
--   St Sheet Form Compare
-- statement:
--   Definitions and structural lemmas for St Sheet Form Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetFormCompare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial Matrix ComplexSets
open scoped ContDiff
noncomputable section
def SheetFormCompare.Statement : Prop :=
  ∀ (n D : ℕ) (h : HermNorm n) (c : Fin D → ℝ) (ψ : Fin D → (Fin n → ℂ) → ℝ),
    (∀ (k : Fin D) (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → ψ k (t • x) = ψ k x) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      ∃ C : ℝ, ∀ (s : (Fin D → ℂ) → Fin n → ℂ) (U : Set (Fin D → ℂ)) (y : Fin D → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ s U → s y ≠ 0 →
          |ReciprocityTheory.AnForm.maDens (fun k => (fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y| ≤
            C * ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y
end
end GroundTheory.Heights₂.Heights


