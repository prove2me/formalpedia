-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImag
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:27.207974+00:00
-- url     : https://prove2.me/theorems/e021e401-3006-4057-adcb-8934bb794337
-- title:
--   Siegel Matrix Symmetric Posdef Imag
-- statement:
--   Definitions and structural lemmas for Siegel Matrix Symmetric Posdef Imag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SiegelMatrixSymmetricPosdefImag.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
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
namespace GlobalTheory.CompanionTheory.SW.ThW
def ZB {F : Type} [Field F] {ι : Type} {W : Type} (B : Matrix ι ι F) (ρ : W → (F →+* ℝ))
    (P : W → Matrix ι ι ℝ) (τ : W → ℂ) (w : W) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)
end GlobalTheory.CompanionTheory.SW.ThW


