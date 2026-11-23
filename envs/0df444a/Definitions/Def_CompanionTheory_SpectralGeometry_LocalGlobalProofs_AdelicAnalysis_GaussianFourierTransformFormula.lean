-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:03.630829+00:00
-- url     : https://prove2.me/theorems/404a794f-2bcc-498d-8d79-3fd6d0e7b5b6
-- title:
--   Gaussian Fourier Transform Formula
-- statement:
--   Definitions and structural lemmas for Gaussian Fourier Transform Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
def swapCurry (α β : Type) : (α × β → ℝ) ≃ᵐ (β → α → ℝ) where
  toFun x := fun b a => x (a, b)
  invFun z := fun p => z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    refine measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun a => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat


