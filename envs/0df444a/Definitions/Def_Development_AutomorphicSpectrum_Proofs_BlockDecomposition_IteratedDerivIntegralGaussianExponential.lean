-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:28.739846+00:00
-- url     : https://prove2.me/theorems/1c86475e-4670-47de-8a7a-a08271bf531a
-- title:
--   Iterated Deriv Integral Gaussian Exponential
-- statement:
--   Definitions and structural lemmas for Iterated Deriv Integral Gaussian Exponential, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
noncomputable def dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian


