-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:40.963174+00:00
-- url     : https://prove2.me/theorems/68ca73cd-8f05-4bef-b9a7-add81cb60c6e
-- title:
--   Aeval Scale Monomial
-- statement:
--   Definitions and structural lemmas for Aeval Scale Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
def IsUU {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1
def matOf {n : ℕ} (x : Fin n × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => x (i, j)
def hwAt {n : ℕ} (κ : Fin n → ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  eval (fun v => Y v.1 v.2) (hw ℂ le_rfl κ)
section MC
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
def mcF (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ := fockF (rowAct ℂ (iotaC ℂ n k Y).transpose f) f
def genY (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) := Matrix.of fun i j => X (i, j)
def mcP : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ m ∈ f.support, (rowAct (MvPolynomial (Fin n × Fin n) ℂ) (iotaC _ n k (genY n)).transpose
      (map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) f)).coeff m * C (star (f.coeff m) * fct m)
variable {f}
end MC
end PI.WGB


