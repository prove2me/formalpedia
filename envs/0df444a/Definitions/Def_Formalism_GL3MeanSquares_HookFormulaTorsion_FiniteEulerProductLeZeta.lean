-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:11.161012+00:00
-- url     : https://prove2.me/theorems/e8b67d00-31e5-4d74-a98f-ac5c600a74ef
-- title:
--   Finite Euler Product Le Zeta
-- statement:
--   Definitions and structural lemmas for Finite Euler Product Le Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/FiniteEulerProductLeZeta.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
noncomputable def invPowMonoidHom (M : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ)⁻¹) ^ M
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv, mul_pow]
end Formalism.HermitianLattices.GenusMassVolumes


