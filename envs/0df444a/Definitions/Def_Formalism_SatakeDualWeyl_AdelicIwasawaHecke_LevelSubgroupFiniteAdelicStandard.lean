-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:13.313924+00:00
-- url     : https://prove2.me/theorems/5e1a67a7-b6e9-4f2d-a4fb-e76a1589b7b8
-- title:
--   Level Subgroup Finite Adelic Standard
-- statement:
--   Definitions and structural lemmas for Level Subgroup Finite Adelic Standard, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Theorems.Thm_P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
def easyc_fstAdd : ↥(stdLat (n := Fin 2) (A := ℚ) ℤ) →+ ZMod 2 where
  toFun x := (((x : Fin 2 → ℚ) 0).num : ZMod 2)
  map_zero' := by simp
  map_add' := by
    intro x y
    obtain ⟨a, ha⟩ := (mem_stdLat_iff' (R := ℤ) (x : Fin 2 → ℚ)).1 x.2 0
    obtain ⟨b, hb⟩ := (mem_stdLat_iff' (R := ℤ) (y : Fin 2 → ℚ)).1 y.2 0
    simp only [algebraMap_int_eq, eq_intCast] at ha hb
    simp only [Submodule.coe_add, Pi.add_apply, ← ha, ← hb]
    rw [← Int.cast_add, Rat.num_intCast, Rat.num_intCast, Rat.num_intCast]
    push_cast; rfl
def easyc_fst : ↥(stdLat (n := Fin 2) (A := ℚ) ℤ) →ₗ[ℤ] ZMod 2 := easyc_fstAdd.toIntLinearMap
def easyc_swap : GL (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
section Lattice
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
end Lattice
end Formalism.UG.P


