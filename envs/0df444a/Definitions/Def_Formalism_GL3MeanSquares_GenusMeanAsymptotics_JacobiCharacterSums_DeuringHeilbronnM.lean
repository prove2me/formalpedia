-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:43.734933+00:00
-- url     : https://prove2.me/theorems/1c8d2d03-ec8a-40d3-ad6c-9057e7687040
-- title:
--   Deuring Heilbronn M
-- statement:
--   Definitions and structural lemmas for Deuring Heilbronn M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/DeuringHeilbronnM.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet

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
def cZ : ℝ := min (Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet) (1 / 20)
def eOf (M : ℕ) [NeZero M] : Option (DirichletCharacter ℂ M × ℝ) :=
  if h : ∃ p : DirichletCharacter ℂ M × ℝ, IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ) then some h.choose
  else if h' : ∃ p : DirichletCharacter ℂ M × ℝ, IsExcPair p.1 p.2 then some h'.choose else none
def etaOf (M : ℕ) [NeZero M] : ℝ :=
  match eOf M with
  | none => 1
  | some (_, β₁) => min 1 ((1 - β₁) * Real.log M)
def mainPsi {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  (if χ = 1 then (y : ℂ) else 0) -
    (match e with
     | none => 0
     | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0)
def excW {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) : ℕ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ ∧ ρ = (β₁ : ℂ) then 1 else 0
def PsiRel : Prop :=
  ∃ c A C₀ : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))
def PsiRelA : Prop :=
  ∃ cA c A : ℝ, 0 < cA ∧ 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    Real.log M ≤ cA * Real.sqrt (Real.log y) →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * Real.exp (-(c * Real.sqrt (Real.log y)))
def PsiRelB (cA : ℝ) : Prop :=
  ∃ c A C₀ : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M → ∀ y : ℝ, 2 ≤ y →
    C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y → cA * Real.sqrt (Real.log y) < Real.log M →
    ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      A * y * etaOf M * Real.exp (-(c * Real.log y / Real.log M))
def ExplicitS : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 → ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (K : ℂ),
      (∀ ρ ∈ Z, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ T + 1) ∧
      (∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∀ t : ℝ, ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), m ρ : ℕ) : ℝ) ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) ∧
      ∀ y : ℝ, 2 ≤ y →
        ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                  ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
          C * (((M : ℝ) * T) ^ C * y ^ (-(κ / 2)) + Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T)
def SharpenS : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (Z : Finset ℂ) (m : ℂ → ℕ) (K : ℂ) (E y δ : ℝ),
    (∀ ρ ∈ Z, 1 / 2 ≤ ρ.re ∧ ρ.re < 1) → 2 ≤ y → 0 < δ → δ ≤ 1 / 2 →
    (∀ u : ℝ, (u = y ∨ u = (1 + δ) * y) →
      ‖Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - K - (if χ = 1 then ((Real.log u - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (u : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤ E) →
    ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) + 4 * (δ * y + 1) * Real.log (2 * y)
def LogDensityM : Prop :=
  ∃ A B C : ℝ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 1 / 2 ≤ σ →
    (∀ p ∈ S, σ ≤ p.2.re ∧ |p.2.im| ≤ T ∧ IsLZero p.1 p.2) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((M : ℝ) * T) ^ B
def DeuringHeilbronnM : Prop :=
  ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → β₁ < 1 →
    IsLZero χ ρ → 1 - c₀ ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T))) / Real.log ((M : ℝ) * T) ≤ 1 - ρ.re
def ZeroSum : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 20 ∧ ∀ C₁ A₁ : ℝ, 1 ≤ A₁ → ∃ c A C₀ : ℝ, 0 < c ∧
    ∀ (M : ℕ) [NeZero M] (Z : DirichletCharacter ℂ M → Finset ℂ) (m : DirichletCharacter ℂ M → ℂ → ℕ),
    8 ∣ M →
    (∀ χ, ∀ ρ ∈ Z χ, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ (M : ℝ) ^ A₁ + 1) →
    (∀ χ, ∀ ρ ∈ Z χ, 1 ≤ m χ ρ) →
    (∀ χ, ∀ ρ ∈ Z χ, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m χ ρ = 1) →
    (∀ χ, ∀ t : ℝ, ((∑ ρ ∈ (Z χ).filter (fun ρ => |ρ.im - t| ≤ 1), m χ ρ : ℕ) : ℝ) ≤
      C₁ * Real.log ((M : ℝ) * (|t| + 2))) →
    ∀ y : ℝ, 2 ≤ y → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
        A * etaOf M * Real.exp (-(c * Real.log y / Real.log M))
def GlueOf : Prop := PsiRelA → (∀ cA : ℝ, 0 < cA → PsiRelB cA) → PsiRel
def PiOf : Prop := PsiRel → PNTAPRelW
def ZeroSumOf : Prop := LogDensityM → DeuringHeilbronnM → ZeroSum
def PsiRelBOf : Prop := ExplicitS → SharpenS → ZeroSum → ∀ cA : ℝ, 0 < cA → PsiRelB cA
end Formalism.HermitianLattices.Ext.PrimesInProgressions


