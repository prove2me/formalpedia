-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussianMomentRealCoords
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussianMomentRealCoords
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:22.020814+00:00
-- url     : https://prove2.me/theorems/46b4f835-dd93-47bb-9f37-75bcae79e963
-- title:
--   Gaussian Moment Real Coords
-- statement:
--   Definitions and structural lemmas for Gaussian Moment Real Coords, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
namespace PositivityTheory.SiegelWeilFormula.KLI
def phi1 (sg : ℤˣ) (t z ξ : ℂ) (α β : ℕ) (w : ℂ) : ℂ :=
  w ^ α * star w ^ β * (cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z * (normSq w : ℂ)) *
    cexp (2 * Real.pi * I * ((t * (star ξ * w)).re : ℂ)))
def Rab (α β : ℕ) : MvPolynomial (Fin 2) ℂ := (X 0 + C I * X 1) ^ α * (X 0 - C I * X 1) ^ β
def lamF (t ξ : ℂ) : ℂ := 2 * Real.pi * I * ((t * star ξ).re : ℂ)
def muF (t ξ : ℂ) : ℂ := -(2 * Real.pi * I * ((t * star ξ).im : ℂ))
end PositivityTheory.SiegelWeilFormula.KLI
end


