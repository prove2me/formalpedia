-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:14.279463+00:00
-- url     : https://prove2.me/theorems/a8770d86-3885-4746-9262-13a3422cbb38
-- title:
--   DHFinish2 Of
-- statement:
--   Definitions and structural lemmas for DHFinish2 Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DHFinish2Of.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHBSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
def DHTuran2 : Prop :=
  ∃ (C : ℝ) (A : ℕ), 0 < C ∧ 1 ≤ A ∧ ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + A * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (A * n) ≤ ‖∑ i, z i ^ k‖
def DHDom : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I) + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ ≤
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re
def DHIneqF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    19 / 20 ≤ β₁ → β₁ < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    0 < η → η ≤ 2 / 25 →
    ∃ (N : ℕ) (w : Fin N → ℂ),
      (∀ i, η ≤ (w i).re) ∧
      (∃ i, w i = ((η + (1 - ρ.re) : ℝ) : ℂ)) ∧
      (∑ i, 1 / w i).re ≤ 2 * (1 - β₁) / η ^ 2 + C * Real.log ((M : ℝ) * T) * 25 ∧
      ∀ j : ℕ, 1 ≤ j →
        ‖∑ i, 1 / (w i) ^ j‖ ≤
          ((-1 : ℂ) ^ (j - 1) * (iteratedDeriv (j - 1) (negLD (1 : DirichletCharacter ℂ M)) ((1 + η : ℝ) : ℂ)
              + iteratedDeriv (j - 1) (negLD χ₁) ((1 + η : ℝ) : ℂ))).re / ((j - 1).factorial : ℝ)
          + 2 * j * (1 - β₁) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j
def DHHyper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (y x : ℝ), 3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
    1 ≤ y → y ≤ x →
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
      ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y) + C * M * (Real.log y + 1) / Real.sqrt y
def DHPrime : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ σ : ℝ) (k : ℕ),
    3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 → 1 < σ → σ ≤ 2 →
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1))
def DHIneqFOf : Prop := DHPos → DHLocal → DHDom → DHIneqF
def DHPrimeOf : Prop := DHHyper → DHPrime
def DHFinish2Of : Prop := DHTuran2 → DHIneqF → DHPrime → DeuringHeilbronnMB
end Formalism.HermitianLattices.Ext.PrimesInProgressions


