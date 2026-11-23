-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExp
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:36.859871+00:00
-- url     : https://prove2.me/theorems/7c80eb35-e2b9-43c8-b543-29f78c534bfc
-- title:
--   Fourier Comp Coord Dilation By Half Exp
-- statement:
--   Definitions and structural lemmas for Fourier Comp Coord Dilation By Half Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierCompCoordDilationByHalfExp.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
namespace GlobalTheory.HeckePoisson.Dilation
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
def dilPi (y : I → ℝ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Real.exp (y i / 2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)
def dilE (y : I → ℝ) : EuclideanSpace ℂ I →ₗ[ℝ] EuclideanSpace ℂ I :=
  ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm : (I → ℂ) →ₗ[ℝ] EuclideanSpace ℂ I) ∘ₗ dilPi y ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm.symm : EuclideanSpace ℂ I →ₗ[ℝ] (I → ℂ))
end GlobalTheory.HeckePoisson.Dilation


