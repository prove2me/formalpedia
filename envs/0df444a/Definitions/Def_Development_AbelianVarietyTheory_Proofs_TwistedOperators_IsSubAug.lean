-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:44.00512+00:00
-- url     : https://prove2.me/theorems/adb52201-c9de-4a3a-a712-04de8ad7568d
-- title:
--   Is Sub Aug
-- statement:
--   Definitions and structural lemmas for Is Sub Aug, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil
namespace GlobalTheory.ThetaGLSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable (m : ℕ) in

def aug (χ : GL (Fin n) k →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) :=
  Submodule.span ℂ {z | ∃ h : GL (Fin n) k, ∃ Φ ∈ SB (Matrix (Fin n) (Fin m) k),
    z = om 1 (1 : GL (Fin m) k) h Φ - (χ h : ℂ) • Φ}
def IsSub {m : ℕ} (χ : GL (Fin n) k →* ℂˣ) (N : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) : Prop :=
  aug m χ ≤ N ∧ N ≤ SB _ ∧ ∀ g : GL (Fin m) k, ∀ Φ ∈ N, om 1 g (1 : GL (Fin n) k) Φ ∈ N
variable {m : ℕ}
end GlobalTheory.ThetaGLSub


