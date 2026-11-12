-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:24:22.424466+00:00
-- url     : https://prove2.me/theorems/95c160a9-03ed-4969-b0ff-5804e74b0441
-- title:
--   Skew Compatibility
-- statement:
--   Definitions and structural lemmas for Skew Compatibility, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewCompatibility.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def cyclicGeneratorCyclicUnit
    (P : BasePrime) (r : Rank) : (CyclicAlgebra P r)ˣ where
  val := cyclicGeneratorCyclicElement P r
  inv := cyclicGeneratorInverseCyclicElement P r
  val_inv := Subtype.ext (cyclicGenerator_mul_inverse P r)
  inv_val := Subtype.ext (cyclicGenerator_inverse_mul P r)
theorem cyclicGeneratorCyclicUnit_zpow_coe
    (P : BasePrime) (r : Rank) (n : ℤ) :
    ((cyclicGeneratorCyclicUnit P r ^ n : (CyclicAlgebra P r)ˣ) :
        CyclicAlgebra P r).1 =
      globalCyclicZMatrixHom P r (Multiplicative.ofAdd n) := by
  let F : (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
    Units.map (CyclicAlgebra P r).val.toRingHom
  have hgen : F (cyclicGeneratorCyclicUnit P r) = cyclicGenerator P r := by
    apply Units.ext
    rfl
  have hp := map_zpow F (cyclicGeneratorCyclicUnit P r) n
  rw [hgen] at hp
  exact congrArg Units.val hp
theorem globalCyclicZMatrixHom_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    globalCyclicZMatrixHom P r n ∈ CyclicAlgebra P r := by
  have hn : n = Multiplicative.ofAdd n.toAdd := rfl
  rw [hn, ← cyclicGeneratorCyclicUnit_zpow_coe P r n.toAdd]
  exact (cyclicGeneratorCyclicUnit P r ^ n.toAdd).1.property
theorem skewLaurentToGlobalMatrix_mem_cyclicAlgebra
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    skewLaurentToGlobalMatrix P r f ∈ CyclicAlgebra P r := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => exact (CyclicAlgebra P r).zero_mem
  | add f g hf hg =>
      rw [map_add]
      exact (CyclicAlgebra P r).add_mem hf hg
  | single n c =>
      rw [skewLaurentToGlobalMatrix_single]
      exact (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        (globalCyclicZMatrixHom_mem_cyclicAlgebra P r n)
noncomputable def skewLaurentToCyclicAlgebra
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSkewLaurentRing P r →+* CyclicAlgebra P r :=
  (skewLaurentToGlobalMatrix P r).codRestrict
    (CyclicAlgebra P r)
    (skewLaurentToGlobalMatrix_mem_cyclicAlgebra P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


