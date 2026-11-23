-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:47.375807+00:00
-- url     : https://prove2.me/theorems/7a3ebf19-2d21-46be-8a4c-3a481c68c393
-- title:
--   Integral Dens Eq Zero
-- statement:
--   Definitions and structural lemmas for Integral Dens Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
def chi (H : Sesq V) (x y : V) : ℂ := cexp (-(2 * Real.pi * I * (altE H x y : ℂ)))
variable {α : V → ℂ}
def dens (H : Sesq V) (F G : V → ℂ) (z : V) : ℂ := F z * conj (G z) * cexp (-(Real.pi : ℂ) * H z z)
def rho (H : Sesq V) (F : V → ℂ) (z : V) : ℝ := ‖F z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re)
section Analytic
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
omit [FiniteDimensional ℝ W] in
theorem real_smul_eq (t : ℝ) (x : W) : t • x = (t : ℂ) • x := (algebraMap_smul ℂ t x).symm
omit [FiniteDimensional ℝ W] in
theorem altE_real_smul_left (t : ℝ) (x y : W) : altE H (t • x) y = t * altE H x y := by
  rw [real_smul_eq t, altE, altE, map_smul]
  simp
def altL (H : Sesq W) (y : W) : W →ₗ[ℝ] ℝ where
  toFun x := altE H x y
  map_add' x x' := by simp [altE]
  map_smul' t x := altE_real_smul_left t x y
variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]
def mean (A : AddSubgroup W) (f : W → ℝ) : ℝ :=
  ⨍ z in Classical.epsilon (fun Fd => IsAddFundamentalDomain A Fd μ), f z ∂μ
end Analytic
end GlobalTheory.ThetaInter


