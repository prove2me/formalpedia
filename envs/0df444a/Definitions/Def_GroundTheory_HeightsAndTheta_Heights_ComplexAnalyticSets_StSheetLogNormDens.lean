-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetLogNormDens
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetLogNormDens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:37.510053+00:00
-- url     : https://prove2.me/theorems/08ce560a-143f-4eee-93ff-b0901b81bb4c
-- title:
--   St Sheet Log Norm Dens
-- statement:
--   Definitions and structural lemmas for St Sheet Log Norm Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetLogNormDens.lean

import Mathlib
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
open MvPolynomial Matrix ComplexSets
noncomputable section
def SheetLogNormDens.Statement : Prop :=
  ∀ (n d m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) (T : Fin d → Matrix (Fin m) (Fin n) ℂ),
    IsSheetAt J A x s → (∀ k, T k *ᵥ x ≠ 0) →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s) (A *ᵥ x)
end
end GroundTheory.Heights₂.Heights


