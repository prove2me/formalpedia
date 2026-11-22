-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
-- name    : Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:35.507935+00:00
-- url     : https://prove2.me/theorems/66ff4631-6c8c-45cc-a1bb-76fb2814e1c9
-- title:
--   Siegel Walfisz AP
-- statement:
--   Definitions and structural lemmas for Siegel Walfisz AP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/SiegelWalfiszAP.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_Statement
import Definitions.Def_Formalism_TwistFamilyExistence_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
namespace Formalism.ZeroFreeDirichlet
def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)
def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]), Λ n
def ExcZeros (c₁ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) : Prop :=
  B.card ≤ 1 ∧
  (∀ β ∈ B, χ ≠ 1 ∧ InRegion c₁ q (β : ℂ) ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
    deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0) ∧
  ∀ s : ℂ, InRegion c₁ q s → IsLZero χ s → ∃ β ∈ B, s = (β : ℂ)
def PsiChiBound : Prop :=
  ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros c₁ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))
def SiegelLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
    c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖
def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x → (q : ℝ) ≤ Real.log x ^ A →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))
def SiegelWalfiszAP : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧
    ∀ (q a : ℕ) (x : ℝ), 1 ≤ q → Nat.Coprime a q → 2 ≤ x → (q : ℝ) ≤ Real.log x ^ A →
      |psiAP q a x - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))
def PrimeShareSW : Prop :=
  ∀ A : ℝ, 0 < A → ∃ κ₀ D₀ : ℝ, 0 < κ₀ ∧
    ∀ D z : ℝ, D₀ ≤ D → 2 ≤ z → z < D → ∀ M r : ℕ, Odd M → Nat.Coprime r (8 * M) →
      ((8 * M : ℕ) : ℝ) ≤ Real.log D ^ A →
      Formalism.TwistFamilyExistence₂.PrimeShare (κ₀ * Real.log z / Real.log D) ((Formalism.WT.DD D z M r).filter Nat.Prime) D z M r
end Formalism.ZeroFreeDirichlet


