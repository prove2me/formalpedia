-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:49.004909+00:00
-- url     : https://prove2.me/theorems/a43013f6-d608-47a0-8583-4a59c331f489
-- title:
--   St Ma Dens Log Pow
-- statement:
--   Definitions and structural lemmas for St Ma Dens Log Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StMaDensLogPow.lean

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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ComplexSets
noncomputable section
def MaDensLogPow.Statement : Prop :=
  ∀ (e : ℕ) (φ₀ p : (Fin (e + 1 + 1) → ℂ) → ℝ) (y : Fin (e + 1 + 1) → ℂ),
    ContDiffAt ℝ 2 p y → 0 < p y →
      maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p) y =
        maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => p) y / p y ^ (e + 1) -
          ((e + 1 : ℕ) : ℝ) * gradDens (Fin.cons φ₀ fun _ : Fin e => p) p p y / p y ^ (e + 2)
end
end GroundTheory.Heights₂.Heights


