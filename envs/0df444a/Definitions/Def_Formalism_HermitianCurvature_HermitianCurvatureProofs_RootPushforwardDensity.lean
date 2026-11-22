-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:01:46.590141+00:00
-- url     : https://prove2.me/theorems/7cd10e3d-0970-4760-b2fa-2c732c2cbe0f
-- title:
--   Root Pushforward Density
-- statement:
--   Definitions and structural lemmas for Root Pushforward Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RootPushforwardDensity.lean

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
def zeta (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)
def R (s k : ℕ) (w : ℂ) : ℂ := zeta s ^ k * w ^ ((s : ℂ)⁻¹)
def A (s k : ℕ) : Set ℂ := {z | z ≠ 0 ∧ R s k (z ^ s) = z}
end Formalism.FourierDecayAlt.P.NthRootMeasurability


