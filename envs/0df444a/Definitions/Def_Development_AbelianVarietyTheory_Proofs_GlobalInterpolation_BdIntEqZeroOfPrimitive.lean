-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:24.539957+00:00
-- url     : https://prove2.me/theorems/0e1d99a4-ff30-46f7-815e-303941a82df6
-- title:
--   Bd Int Eq Zero Of Primitive
-- statement:
--   Definitions and structural lemmas for Bd Int Eq Zero Of Primitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory.ResRect
noncomputable def bdInt (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I))
    + I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))
def SidesIn (a b c d : ℝ) (B : Set ℂ) : Prop :=
  (∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) ∧ (∀ x ∈ Set.uIcc a b, (x : ℂ) + d * I ∈ B) ∧
  (∀ y ∈ Set.uIcc c d, (b : ℂ) + y * I ∈ B) ∧ (∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B)
end GlobalTheory.ResRect


