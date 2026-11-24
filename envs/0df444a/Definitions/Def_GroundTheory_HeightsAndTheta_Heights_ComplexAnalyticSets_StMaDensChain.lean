-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:58.159482+00:00
-- url     : https://prove2.me/theorems/04039784-070a-46d3-a2a3-515653a7c425
-- title:
--   St Ma Dens Chain
-- statement:
--   Definitions and structural lemmas for St Ma Dens Chain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StMaDensChain.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
def MaDensChain.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (F : ℝ → ℝ) (g : (Fin (D + 1) → ℂ) → ℝ)
    (z : Fin (D + 1) → ℂ),
    ContDiff ℝ 2 F → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (F ∘ g) φ) z =
          deriv F (g z) * maDens (Fin.cons g φ) z + deriv (deriv F) (g z) * gradDens φ g g z ∧
        gradDens φ (F ∘ g) (F ∘ g) z = deriv F (g z) ^ 2 * gradDens φ g g z
end
end GroundTheory.Heights₂.Heights


