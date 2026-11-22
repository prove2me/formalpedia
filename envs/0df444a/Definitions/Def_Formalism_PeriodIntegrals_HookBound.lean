-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HookBound
-- name    : Formalism_PeriodIntegrals_HookBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:12.709167+00:00
-- url     : https://prove2.me/theorems/be163e5e-3fa3-43aa-b1f1-acb5a21aa48c
-- title:
--   Hook Bound
-- statement:
--   Definitions and structural lemmas for Hook Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HookBound.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
def stdGram {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    Formalism.GradedWeylDivisibility.fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ))
              (MvPolynomial.map (Int.castRingHom ℚ) (e j : MvPolynomial (Fin N × Fin N) ℤ)) /
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν)
def MuStd {N : ℕ} (ν : Fin N → ℕ) (μ : ℝ) : Prop :=
  ∃ (r : ℕ) (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)), 0 < r ∧
    μ = -Real.log ((stdGram ν e).det : ℝ) / r
def cNu {N : ℕ} (ν : Fin N → ℕ) : ℝ :=
  (Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) : ℝ) / ∏ l, ((ν l).factorial : ℝ)
def HookBound : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ), Antitone ν →
    1 ≤ cNu ν ∧ cNu ν ≤ ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2)
def StdSlopeLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (μ : ℝ), Antitone ν → MuStd ν μ →
    -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) ≤ μ
end PI


