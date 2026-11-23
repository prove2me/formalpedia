-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:21.104783+00:00
-- url     : https://prove2.me/theorems/386db5b3-59d4-4afd-a0d8-83d37e2a1a24
-- title:
--   Fp Dual Unram
-- statement:
--   Definitions and structural lemmas for Fp Dual Unram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/FpDualUnram.lean

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
open ValuativeRel
namespace PI.LocDualGen.W
def PsiKer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (t : ℚ_[l]) (a : ℚ), (∃ n : ℕ, a.den = l ^ n) → ‖t - (a : ℚ_[l])‖ ≤ 1 →
    (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ ‖t‖ ≤ 1)
def FpDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K]
def FpDualUnram : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    Irreducible ((l : ℕ) : 𝒪[K]) →
    ∀ a : K, (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K))‖ ≤ 1) ↔ a ∈ 𝒪[K]
def EpSelfDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (L : Type) [CommRing L]
    [Algebra K L], IsNonarchimedeanLocalField K → CharZero K →
    Module.Free K L → Module.finrank K L = 2 → IsReduced L →
    ∀ O : Subring L, (∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x) →
    (∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)}) →
    ∀ x : L, (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O
end PI.LocDualGen.W


