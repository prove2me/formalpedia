-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
-- name    : Formalism_PeriodIntegrals_FockDegreeTwoParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:32.384444+00:00
-- url     : https://prove2.me/theorems/ce0d2d8d-151c-484c-9d93-90168a211bec
-- title:
--   Fock Degree Two Parts
-- statement:
--   Definitions and structural lemmas for Fock Degree Two Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FockDegreeTwoParts.lean

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
namespace PI.FockDegreeTwoParts
def WtDeg : Prop := ∀ p q r s : ℕ,
  (∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct1 p q r s) μ P →
    degW (cPair r s) μ ≤ d) ∧
  (∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct2 p q r s) μ P →
    degW (cPair p q) μ ≤ d)
def OneDeg : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d)
def JointMult : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s)) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s) = ⊥))
def HarmSplit : Prop := ∀ p q r s : ℕ,
  (∀ (u1 u2 : Bool), (u1 || u2) = true → ∀ d : ℕ,
    homog (Ix p q × Ix r s) (d + 2) =
      (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (lowKer p q r s u1 u2)) ⊔
      Submodule.span ℂ (raised p q r s u1 u2 d))
end PI.FockDegreeTwoParts


