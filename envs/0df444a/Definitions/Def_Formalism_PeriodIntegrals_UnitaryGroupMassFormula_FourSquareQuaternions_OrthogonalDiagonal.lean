-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:46.990827+00:00
-- url     : https://prove2.me/theorems/6010bbd6-40fd-4906-85f5-6b4646596d3c
-- title:
--   Orthogonal Diagonal
-- statement:
--   Definitions and structural lemmas for Orthogonal Diagonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
namespace PI.KerIso.FourSqW
section Conj
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
def conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : K := Classical.choose (hc.2.1 k)
theorem conjFun_spec (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    algebraMap K E (conjFun cj hc k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (hc.2.1 k)).symm
theorem conjFun_conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    conjFun cj hc (conjFun cj hc k) = k :=
  (algebraMap K E).injective (by rw [conjFun_spec, conjFun_spec, hc.1])
def conjK (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) : K ≃+* K where
  toFun := conjFun cj hc
  invFun := conjFun cj hc
  left_inv := conjFun_conjFun cj hc
  right_inv := conjFun_conjFun cj hc
  map_mul' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_mul, map_mul, map_mul, conjFun_spec, conjFun_spec])
  map_add' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_add, map_add, map_add, conjFun_spec, conjFun_spec])
end Conj
section Orth
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
def trL (cj : E ≃ₐ[ℚ] E) (y : E) : E →ₗ[K] K :=
  (Algebra.trace K E).comp (LinearMap.mulRight K (cj y))
end Orth
end PI.KerIso.FourSqW


