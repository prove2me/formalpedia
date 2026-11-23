-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:15.47107+00:00
-- url     : https://prove2.me/theorems/b46d0a65-127c-47a8-b36c-80ef18b7d7c3
-- title:
--   Is Exc Rat
-- statement:
--   Definitions and structural lemmas for Is Exc Rat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/IsExcRat.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.An
def IsExcRat {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (β : ℝ) : Prop :=
  χ ^ 2 = 1 ∧ 1 - 1 / (8 * Real.log M) < β ∧ β < 1 ∧
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ.primitiveCharacter β = 0
def TZRat : Prop :=
  ∃ c₂ c₃ CA cS : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → M % 4 ≠ 2 →
    (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExcRat χ β → IsExcRat χ' β' → χ = χ' ∧ β = β') ∧
    (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExcRat χ β → cS / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧
    ∀ (b : ℕ) (θ : ℤ) (β : ℝ), Nat.Coprime b M →
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExcRat χ β') ∨
        ∃ χ : DirichletCharacter ℂ M, IsExcRat χ β ∧ χ (b : ZMod M) = (θ : ℂ)) →
      ∀ X : ℝ, (M : ℝ) ^ c₂ ≤ X →
        |(M.totient : ℝ) * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X
end GlobalTheory.Mem.An


