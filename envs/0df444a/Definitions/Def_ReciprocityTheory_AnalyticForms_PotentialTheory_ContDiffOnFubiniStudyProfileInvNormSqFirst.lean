-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:11.574134+00:00
-- url     : https://prove2.me/theorems/27513cf7-c93e-4571-8dce-e1ceb344a840
-- title:
--   Cont Diff On Fubini Study Profile Inv Norm Sq First
-- statement:
--   Definitions and structural lemmas for Cont Diff On Fubini Study Profile Inv Norm Sq First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
def p1Re : (Fin 1 → ℂ) →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)
def p1Im : (Fin 1 → ℂ) →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)
def projectiveLineNormSqDerivative : (Fin 1 → ℂ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
  (2 : ℝ) • (p1Re.smulRight p1Re + p1Im.smulRight p1Im)
def fubiniStudyProfile (t : ℝ) : ℝ := (1 / 2) * Real.log (1 + t)
def fubiniStudyProfileInv (t : ℝ) : ℝ := (1 / 2) * Real.log (1 + t⁻¹)
def fsQ (w : Fin 1 → ℂ) : ℝ := ‖w 0‖ ^ 2
end
end ReciprocityTheory.AnForm.M


