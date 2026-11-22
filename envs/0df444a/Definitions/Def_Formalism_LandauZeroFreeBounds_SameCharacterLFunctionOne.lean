-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
-- name    : Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:27.076824+00:00
-- url     : https://prove2.me/theorems/297e5e18-1820-4b6c-a993-58fc843bcf5b
-- title:
--   Same Character LFunction One
-- statement:
--   Definitions and structural lemmas for Same Character LFunction One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/SameCharacterLFunctionOne.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder
noncomputable section
namespace Formalism.ZeroFreeDirichlet
def IsProdChar {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (ψ : DirichletCharacter ℂ (q₁ * q₂)) : Prop :=
  ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)
def Fbq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
    DirichletCharacter.LFunction ψ s
def lamBq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)) : ℂ :=
  DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction ψ 1
def ProdCharExists : Prop :=
  ∀ (q₁ q₂ : ℕ) (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
    ∃ ψ : DirichletCharacter ℂ (q₁ * q₂), IsProdChar χ₁ χ₂ ψ
def BqCoeff : Prop :=
  ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → IsProdChar χ₁ χ₂ ψ →
    ∃ a : ℕ → ℂ, (∀ n, 0 ≤ a n) ∧ a 1 = 1 ∧ LSeries.abscissaOfAbsConv a ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → Fbq χ₁ χ₂ ψ s = LSeries a s
def BqEntire : Prop :=
  ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)), χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ s : ℂ, s ≠ 1 → Fbq χ₁ χ₂ ψ s = G s + lamBq χ₁ χ₂ ψ / (s - 1)
def BqGrowth : Prop :=
  ∃ C K : ℝ, ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)), χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 →
    ∀ s : ℂ, ‖s - 2‖ = 3 / 2 → ‖Fbq χ₁ χ₂ ψ s‖ ≤ C * ((q₁ * q₂ : ℕ) : ℝ) ^ K
def LFunctionOneUpperBound : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ‖DirichletCharacter.LFunction χ 1‖ ≤ C * Real.log (3 * q)
def BqKey : Prop :=
  ∃ C K : ℝ, 0 ≤ K ∧ ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ₂ ψ →
    ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
      1 / 2 - C * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) ≤ (Fbq χ₁ χ₂ ψ σ).re
def ZetaNegReal : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → (riemannZeta σ).im = 0 ∧ (riemannZeta σ).re < 0
def LRealPos : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ σ₀ : ℝ,
    (∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0) →
    ∀ σ : ℝ, σ₀ ≤ σ → (DirichletCharacter.LFunction χ σ).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ).re
def SameCharacterLFunctionOne : Prop :=
  ∀ (q₁ q : ℕ) [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q),
    χ₁ ≠ 1 → χ ≠ 1 → (∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 *
      ‖DirichletCharacter.LFunction χ 1‖
def RealCharExists : Prop :=
  ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 ∧ χ ≠ 1
def BqKeyOf : Prop := BqCoeff → BqEntire → BqGrowth → LFunctionOneUpperBound → BqKey
def SiegelOf : Prop :=
  ProdCharExists → RealCharExists → BqKey → LFunctionOneUpperBound → ZetaNegReal → LRealPos → SameCharacterLFunctionOne → SiegelLower
end Formalism.ZeroFreeDirichlet


