-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:37.317791+00:00
-- url     : https://prove2.me/theorems/67133565-16be-40b5-9761-7e4740db788b
-- title:
--   Inst Measurable Space Mat
-- statement:
--   Definitions and structural lemmas for Inst Measurable Space Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/InstMeasurableSpaceMat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SchurFock
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory
instance instMeasurableSpaceMat (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℂ) := borel _
instance instBorelSpaceMat (N : ℕ) : BorelSpace (Matrix (Fin N) (Fin N) ℂ) := ⟨rfl⟩
def evalM {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s
def EvalOne : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam, evalM 1 s = normFock lam s (extremal ℂ N lam)
def IsHaarU (N : ℕ) (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ, x ∈ Matrix.unitaryGroup (Fin N) ℂ) ∧
  (∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : Matrix (Fin N) (Fin N) ℂ → ℂ, Continuous f →
    ∫ x, f (x * u) ∂μ = ∫ x, f x ∂μ) ∧
  (∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : Matrix (Fin N) (Fin N) ℂ → ℂ, Continuous f →
    ∫ x, f (u * x) ∂μ = ∫ x, f x ∂μ)
def HaarU : Prop := ∀ N : ℕ, ∃ μ : Measure (Matrix (Fin N) (Fin N) ℂ), IsHaarU N μ
def SchurOrth : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N) (μ : Measure (Matrix (Fin N) (Fin N) ℂ)), IsHaarU N μ →
    ∀ s ∈ nablaSq ℂ N lam,
      (normFock lam s s).re = (Module.finrank ℂ (delSq ℂ N lam) : ℝ) * ∫ x, ‖evalM x s‖ ^ 2 ∂μ
end PI.WSF


