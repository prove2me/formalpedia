-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:27.957883+00:00
-- url     : https://prove2.me/theorems/93b03dcd-1a0b-4642-acd1-f79b5720ab76
-- title:
--   Finrank Inf Ker Add One
-- statement:
--   Definitions and structural lemmas for Finrank Inf Ker Add One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
namespace DensInertW.Sub
variable {L : Type} [Field L]
def sig (q : ℕ) (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) : L →+* L where
  toFun a := a ^ q
  map_one' := one_pow q
  map_mul' a b := mul_pow a b q
  map_zero' := zero_pow hq
  map_add' := hadd
section
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
theorem hf_add_left (x x' y : Fin n → L) : hf q M (x + x') y = hf q M x y + hf q M x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem hf_smul_left (c : L) (x y : Fin n → L) : hf q M (c • x) y = c * hf q M x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring
def hfL (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L) : (Fin n → L) →ₗ[L] L where
  toFun x := hf q M x y
  map_add' x x' := hf_add_left x x' y
  map_smul' c x := by simp only [hf_smul_left, smul_eq_mul, RingHom.id_apply]
end
section geom
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
end geom
end DensInertW.Sub


