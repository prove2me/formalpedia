-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HwIrred
-- name    : Formalism_PeriodIntegrals_HwIrred
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:47.6938+00:00
-- url     : https://prove2.me/theorems/01dd1a83-d74f-4a44-b290-9c576cc3913d
-- title:
--   Hw Irred
-- statement:
--   Definitions and structural lemmas for Hw Irred, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HwIrred.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Formalism.BasicNotions MvPolynomial
def HwIrred : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), nablaSq ℂ N lam = delSq ℂ N lam ∧
    (∀ U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ), U ≤ nablaSq ℂ N lam →
      (∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U) → U = ⊥ ∨ U = nablaSq ℂ N lam) ∧
    ∀ f ∈ nablaSq ℂ N lam,
      (∀ g : GL (Fin N) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) → sqAct ℂ N lam g f = f) →
      ∃ c : ℂ, f = c • extremal ℂ N lam
end PI


