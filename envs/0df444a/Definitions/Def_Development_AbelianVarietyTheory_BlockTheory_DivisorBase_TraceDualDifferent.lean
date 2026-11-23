-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:26.887799+00:00
-- url     : https://prove2.me/theorems/e8bbb972-5e1a-4163-98d3-2562126236df
-- title:
--   Trace Dual Different
-- statement:
--   Definitions and structural lemmas for Trace Dual Different, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean

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
open NumberField nonZeroDivisors
namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
def traceDual (M : FractionalIdeal (𝓞 F)⁰ F) : Set F :=
  {y | ∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n}
def covol (M : FractionalIdeal (𝓞 F)⁰ F) : ℝ :=
  Real.sqrt |(discr F : ℝ)| * (FractionalIdeal.absNorm M : ℝ)
def dualCone (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) : Set F :=
  {ν | ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν}
def lhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (a : F) : ℂ :=
  (∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ))) ^ (-(k : ℤ))
def rhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) : ℂ :=
  ((|∏ τ : F →+* ℝ, τ ν| ^ (k - 1) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * z τ)
def lipConst (k : ℕ) (M : FractionalIdeal (𝓞 F)⁰ F) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (k * Module.finrank ℚ F) /
    ((((k - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * (covol M : ℂ))
def Lipschitz : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
    ∀ (k : ℕ), 2 ≤ k → Even k →
    ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
      Summable (fun a : (M : Set F) => lhsTerm k z a) ∧
      Summable (fun ν : dualCone M z => rhsTerm k z ν) ∧
      ∑' a : (M : Set F), lhsTerm k z a = lipConst k M * ∑' ν : dualCone M z, rhsTerm k z ν
example (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, 0 < (z τ).im) (ν : F) :
    ν ∈ dualCone M z ↔ ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < τ ν := by
  simp [dualCone, hz]
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent


