-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:28.268785+00:00
-- url     : https://prove2.me/theorems/7643f9ed-dd42-404e-8d72-d8f1542c3574
-- title:
--   Red Defs
-- statement:
--   Definitions and structural lemmas for Red Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/RedDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
namespace PI.FockOneDegW
def KHc : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ (e : ℕ) (P : Pol p q r s),
  homogeneousComponent e (fockAct1 p q r s (Eab a b) P) =
    fockAct1 p q r s (Eab a b) (homogeneousComponent e P)
def KHarm : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P : Pol p q r s,
  Harm2 P → Harm2 (fockAct1 p q r s (Eab a b) P)
def HcHarm : Prop := ∀ p q r s : ℕ, ∀ (e : ℕ) (P : Pol p q r s),
  Harm2 P → Harm2 (homogeneousComponent e P)
def HarmSub : Prop := ∀ p q r s : ℕ,
  Harm2 (0 : Pol p q r s) ∧ (∀ P Q : Pol p q r s, Harm2 P → Harm2 Q → Harm2 (P + Q)) ∧
    (∀ (c : ℂ) (P : Pol p q r s), Harm2 P → Harm2 (c • P))
def KAdj : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P Q : Pol p q r s,
  fockInner P (fockAct1 p q r s (Eab a b) Q) = fockInner (fockAct1 p q r s (Eab b a) P) Q
def HwExist : Prop := ∀ p q r s : ℕ, ∀ U : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ U → U ≠ ⊥ →
  (∀ a b : Ix p q, sameBlock a b → ∀ u ∈ U, fockAct1 p q r s (Eab a b) u ∈ U) →
    ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ IsHW (fockAct1 p q r s) ν v
end PI.FockOneDegW


