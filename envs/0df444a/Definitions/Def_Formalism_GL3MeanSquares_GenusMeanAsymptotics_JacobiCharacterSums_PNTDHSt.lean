-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:31.96803+00:00
-- url     : https://prove2.me/theorems/9a9e4640-5aca-4fd8-a161-5d01e77b8567
-- title:
--   PNTDHSt
-- statement:
--   Definitions and structural lemmas for PNTDHSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHSt.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
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
def DHTuran : Prop :=
  ∃ (c : ℝ) (A B : ℕ), 0 < c ∧ ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
    ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c ^ K ≤ (∑ i, z i ^ k).re
def DHPos : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    0 ≤ ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ)
        + iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I))).re
def DHCauchy : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ), 0 < r → 1 ≤ B →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ (k : ℕ) (s : ℂ), s ∈ Metric.closedBall z₀ (r / 12) → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ 72 * Real.log B / r * (12 / r) ^ k
def DHLocal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ), 3 ≤ M →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k
def DHCount : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ C' : ℝ, 0 < C' ∧ ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ)
    (Z : Finset ℂ) (m : ℂ → ℕ), 3 ≤ M → (∀ ρ ∈ Z, ρ.re < 1) →
    (∀ s : ℂ, 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
      ‖negLD ψ s - (if ψ = 1 then 1 / (s - 1) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) →
    ∀ σ R : ℝ, 0 < R → R ≤ 1 / 50 → 1 < σ → σ ≤ 1 + R →
      (∑ ρ ∈ Z.filter (fun ρ => ‖(σ : ℂ) + t * I - ρ‖ ≤ R), (m ρ : ℝ)) ≤
        C' * (R * Real.log ((M : ℝ) * (|t| + 2)) + 1)
def DHIneq : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    19 / 20 ≤ β₁ → β₁ < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    0 < η → η ≤ 2 / 25 →
    ∃ (N : ℕ) (w : Fin N → ℂ),
      (∀ i, η ≤ (w i).re) ∧
      (∃ i, w i = ((η + (1 - ρ.re) : ℝ) : ℂ)) ∧
      ((N : ℝ) ≤ C * Real.log ((M : ℝ) * T)) ∧
      (∀ R : ℝ, η ≤ R → R ≤ 1 / 50 →
        ((Finset.univ.filter (fun i => ‖w i‖ ≤ R)).card : ℝ) ≤ C * (R * Real.log ((M : ℝ) * T) + 1)) ∧
      ∀ j : ℕ, 1 ≤ j →
        (∑ i, 1 / (w i) ^ j).re ≤ 2 * j * (1 - β₁) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j
def DHLocalOf : Prop := DHCauchy → DHLocal
def DHIneqOf : Prop := DHPos → DHLocal → DHCount → DHIneq
def DHFinishOf : Prop := DHTuran → DHIneq → DeuringHeilbronnM
end Formalism.HermitianLattices.Ext.PrimesInProgressions


