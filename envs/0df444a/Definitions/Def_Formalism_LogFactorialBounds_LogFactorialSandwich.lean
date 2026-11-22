-- Prove2me | Definitions.Def_Formalism_LogFactorialBounds_LogFactorialSandwich
-- name    : Formalism_LogFactorialBounds_LogFactorialSandwich
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:52:56.628814+00:00
-- url     : https://prove2.me/theorems/a8c7bc7a-c932-4b7b-8ed1-f17400a2f4f8
-- title:
--   Log Factorial Sandwich
-- statement:
--   Definitions and structural lemmas for Log Factorial Sandwich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialBounds/LogFactorialSandwich.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LogFactorialBounds
open Finset Real
def ph (y : ℝ) : ℝ := y * Real.log y - y
def PhSup : Prop :=
  ∀ ν : ℝ, 0 < ν →
    (∀ s : ℝ, 0 ≤ s → s ^ ν * Real.exp (-(s ^ 2) / 2) ≤ Real.exp (ph ν / 2)) ∧
      (Real.sqrt ν) ^ ν * Real.exp (-((Real.sqrt ν) ^ 2) / 2) = Real.exp (ph ν / 2)
def LogFactorialSandwich : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ph n + Real.log (2 * π * n) / 2 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ ph n + Real.log n / 2 + 1
def PhLipschitz : Prop :=
  ∀ x y Y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ Y → y ≤ Y → |ph x - ph y| ≤ |x - y| * Real.log Y
def PhShift : Prop :=
  ∀ a w : ℝ, 1 ≤ a → 0 ≤ w → 0 ≤ ph (a + w) - ph a ∧ ph (a + w) - ph a ≤ w * Real.log (a + w)
def PhLowerBound : Prop :=
  ∀ y : ℝ, 0 ≤ y → -1 ≤ ph y
def FELogDeriv : Prop :=
  ∀ (L : ℂ → ℂ) (d : ℝ), 0 < d →
    DifferentiableAt ℂ L 0 → DifferentiableAt ℂ L 1 → L 0 ≠ 0 → L 1 ≠ 0 →
    (∀ᶠ s in nhds (0 : ℂ),
        ((d / π : ℝ) : ℂ) ^ ((s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * L s =
          ((d / π : ℝ) : ℂ) ^ (((1 - s) + 1) / 2) * Complex.Gamma (((1 - s) + 1) / 2) * L (1 - s)) →
    logDeriv L 0 =
      -logDeriv L 1 - ((Real.log (d / π) : ℝ) : ℂ) + ((Real.eulerMascheroniConstant : ℝ) : ℂ)
        + ((Real.log 2 : ℝ) : ℂ)
def KWCancelOffTop : Prop :=
  ∀ (n nb j m : ℕ) (c₀ : ℝ) (c c' : Fin n → ℝ) (β : Fin nb → ℝ)
    (w L logOm Sc Bt C₀ U E₃ E₄ logK logLam cov : ℝ),
    1 ≤ w → 0 ≤ c₀ → (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ c' i) → (∀ l, 0 ≤ β l) →
    Real.log (w + c₀) ≤ L → (∀ i, Real.log (w + c i) ≤ L) → (∀ i, Real.log (w + c' i) ≤ L) →
    (∀ l, Real.log (β l) ≤ L) →
    |logOm| ≤ L → (∑ i, |c i - c' i|) ≤ Sc → (∑ l, β l) ≤ Bt →
    logK ≤ ph (w + c₀) + (∑ i, ph (w + c i)) + (∑ l, ph (β l))
        - (((n : ℝ) + 1) * w + c₀ + (∑ i, c i) + (∑ l, β l)) * logOm + E₃ →
    (∑ i, ph (w + c' i)) - E₄ ≤ logLam →
    cov ≤ ((((n : ℝ) + 1) + j - 1) - ((m : ℝ) - j)) * w * logOm + C₀ * U * L →
    logK - logLam + cov ≤
      (2 * (j : ℝ) - 1 - m) * w * logOm
        + (w + 2 * c₀ + (∑ i, c i) + Sc + 2 * Bt) * L + C₀ * U * L + E₃ + E₄
def KWCancelTop : Prop :=
  ∀ (n nb j m : ℕ) (a ρ : ℝ) (c : Fin n → ℝ) (c' : Fin (n + 1) → ℝ) (β : Fin nb → ℝ)
    (w L logOm Sc Bt C₀ U E₃ E₄ logK logLam cov : ℝ),
    1 ≤ w → 1 ≤ a → 0 ≤ ρ → (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ c' i) → (∀ l, 0 ≤ β l) →
    Real.log (a + w) ≤ L → Real.log ρ ≤ L → (∀ i, Real.log (w + c i) ≤ L) →
    (∀ i, Real.log (w + c' i) ≤ L) → (∀ l, Real.log (β l) ≤ L) →
    |logOm| ≤ L → (∑ i : Fin n, |c i - c' (Fin.castSucc i)|) ≤ Sc → (∑ l, β l) ≤ Bt →
    logK ≤ ph (a + w) + (∑ i, ph (w + c i)) + ph ρ + (∑ l, ph (β l))
        - (a + w + (∑ i, (w + c i)) + ρ + (∑ l, β l)) * logOm + E₃ →
    (∑ i, ph (w + c' i)) - E₄ ≤ logLam →
    cov ≤ ((((n : ℝ) + 2) + j - 1) - ((m : ℝ) - j)) * w * logOm + C₀ * U * L →
    logK - logLam + cov ≤
      ph a - a * logOm + (2 * (j : ℝ) - m) * w * logOm
        + (w + Sc + (∑ i, c i) + 2 * ρ + 2 * Bt) * L + C₀ * U * L + E₃ + E₄ + 1
end Formalism.LogFactorialBounds


