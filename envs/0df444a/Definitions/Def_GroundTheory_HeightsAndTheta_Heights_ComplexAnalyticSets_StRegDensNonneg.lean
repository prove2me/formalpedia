-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:24.585128+00:00
-- url     : https://prove2.me/theorems/d6acfa5c-8ba4-4ffe-ae75-f629fa90a55f
-- title:
--   St Reg Dens Nonneg
-- statement:
--   Definitions and structural lemmas for St Reg Dens Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegDensNonneg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def RegDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
    0 < ε → IsSheetAt J A x s →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (vecCons (logReg u ε) fun _ => euclPot : Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ s) (A *ᵥ x)
end
end GroundTheory.Heights₂.Heights


