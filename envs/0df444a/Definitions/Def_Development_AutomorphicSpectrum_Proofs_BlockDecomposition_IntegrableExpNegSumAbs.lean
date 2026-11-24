-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:24.295047+00:00
-- url     : https://prove2.me/theorems/5ac4b0d6-4f80-4181-88a9-3ded7d695dff
-- title:
--   Integrable Exp Neg Sum Abs
-- statement:
--   Definitions and structural lemmas for Integrable Exp Neg Sum Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
namespace GlobalTheory.CompanionTheory.EisTube
noncomputable def ker {ι : Type} [Fintype ι] (z : ι → ℂ) (t : ι → ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)
noncomputable def lin {ι : Type} [Fintype ι] (t : ι → ℝ) : (ι → ℂ) →L[ℂ] ℂ :=
  (2 * (Real.pi : ℂ)) • ∑ i, (t i : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i
end GlobalTheory.CompanionTheory.EisTube


