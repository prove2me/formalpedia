-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:49.144936+00:00
-- url     : https://prove2.me/theorems/2d8cfe9c-9837-4f70-8275-bc14edaf728f
-- title:
--   Completed LStrip Bounds
-- statement:
--   Definitions and structural lemmas for Completed LStrip Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CompletedLStripBounds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
def archFactor (n : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))
def IsCompletedL (χ : HChar E) (n : I → ℤ) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = archFactor n s * L
def BoundedInStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C
def CompletedLBoundedInStrips : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ), IsUnitary χ → Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) →
      ∃ Λ : ℂ → ℂ, IsCompletedL χ n Λ ∧ BoundedInStrips Λ
def CompletedLBoundedInStripsEven : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ), IsUnitary χ → HasInfRatio χ φ m → (∃ i, m i ≠ 0) →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
        (∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = LInf m s * L) ∧ BoundedInStrips Λ
example : ¬ BoundedInStrips (fun s => s) := by
  intro h
  obtain ⟨C, hC⟩ := h 0 1 one_pos
  have := hC (((|C| + 1 : ℝ) : ℂ) * Complex.I) (by simp) (by simp)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith [le_abs_self C]
example : archFactor (fun _ : Unit => (-2 : ℤ)) 0 = (Real.pi : ℂ)⁻¹ := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [archFactor, Complex.cpow_neg_one]
  field_simp
end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds


