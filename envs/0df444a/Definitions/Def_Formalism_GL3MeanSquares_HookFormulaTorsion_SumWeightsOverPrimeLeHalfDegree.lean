-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:47.676935+00:00
-- url     : https://prove2.me/theorems/cb0d4b60-a793-497c-9112-ff85935d0670
-- title:
--   Sum Weights Over Prime Le Half Degree
-- statement:
--   Definitions and structural lemmas for Sum Weights Over Prime Le Half Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SumWeightsOverPrimeLeHalfDegree.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset NumberField
open Formalism.LogVandermondeBounds.StandardLattice
section alg
variable (K : Type) [Field K] [NumberField K]
noncomputable def residueCharacteristic (P : Ideal (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ P)
variable [StarRing K]
end alg
section ana
noncomputable def invPowMonoidHomReal (M : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ)⁻¹) ^ M
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv, mul_pow]
noncomputable def negLogOneSubInvPow (M p : ℕ) : ℝ := -Real.log (1 - ((p : ℝ)⁻¹) ^ M)
end ana
section main
variable (K : Type) [Field K] [NumberField K]
noncomputable def idealPrimeWeight (P : Ideal (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm P : ℝ) / (2 * Real.log (residueCharacteristic K P : ℝ))
variable [StarRing K]
end main
end Formalism.HermitianLattices.GenusMassVolumes


