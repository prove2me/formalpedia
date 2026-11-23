-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
-- name    : Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:46.733357+00:00
-- url     : https://prove2.me/theorems/50baff20-0d54-4f31-adac-f8e841b4b1ec
-- title:
--   Zeros Disc
-- statement:
--   Definitions and structural lemmas for Zeros Disc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ZerosDisc.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
namespace GlobalTheory.Lin
def zerosBox {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Set ℂ :=
  {ρ | σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}
def ord {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
def zerosDisc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c : ℂ) (R : ℝ) : Set ℂ :=
  {w | ‖w - c‖ ≤ R ∧ (χ ≠ 1 ∨ w ≠ 1) ∧ DirichletCharacter.LFunction χ w = 0}
def derSeries (c : ℕ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (n : ℂ) ^ (-s)
def primesIoc (x y : ℝ) : Finset ℕ := (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime
def psiAP (M b : ℕ) (u : ℝ) : ℝ := ∑ n ∈ (Icc 1 ⌊u⌋₊).filter (fun n => n ≡ b [MOD M]), Λ n
def IsExc (c₁ : ℝ) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (β : ℝ) : Prop :=
  χ ^ 2 = 1 ∧ 1 - c₁ / Real.log M < β ∧ β < 1 ∧
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ.primitiveCharacter β = 0
def ExcData (c₁ : ℝ) (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β : ℝ) : Prop :=
  (θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExc c₁ χ β') ∨
    ∃ χ : DirichletCharacter ℂ M, IsExc c₁ χ β ∧ χ (b : ZMod M) = (θ : ℂ)
def PrimesRel : Prop :=
  ∃ c₁ c₂ c₃ CA cS : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 8 ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M →
    (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧
    (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → cS / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧
    ∀ (b : ℕ) (θ : ℤ) (β : ℝ), Nat.Coprime b M → ExcData c₁ M b θ β →
      ∀ X : ℝ, (M : ℝ) ^ c₂ ≤ X →
        |(M.totient : ℝ) * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X
end GlobalTheory.Lin
end


