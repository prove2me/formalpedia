-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:33:40.541646+00:00
-- url     : https://prove2.me/theorems/86b8c4a7-071f-4056-8171-cd97636bd6b6
-- title:
--   Global Building Lattice
-- statement:
--   Definitions and structural lemmas for Global Building Lattice, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/GlobalBuildingLattice.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem cartwrightStegerOrder_le_cyclicAlgebra
    (P : BasePrime) (r : Rank) :
    ∀ M, M ∈ CartwrightStegerOrder P r → M ∈ CyclicAlgebra P r := by
  intro M hM
  apply Algebra.adjoin_induction
    (R := ArithmeticRing P)
    (s := Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
    (p := fun M _ => M ∈ CyclicAlgebra P r)
  · intro N hN
    rcases hN with hN | hN
    · obtain ⟨c, rfl⟩ := hN
      exact constantMatrix_mem_cyclicAlgebra P r c
    · rcases hN with (rfl | hN)
      · exact cyclicGeneratorMatrix_mem_cyclicAlgebra P r
      · rw [Set.mem_singleton_iff] at hN
        subst N
        exact cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r
  · intro a
    have ha := (CyclicAlgebra P r).algebraMap_mem
      (arithmeticRingToFunctionField P a)
    change arithmeticRingToSplitMatrix P r a ∈ CyclicAlgebra P r
    change Matrix.scalar (Fin r.matrixRank)
        (functionFieldEmbedding P r (arithmeticRingToFunctionField P a)) ∈
      CyclicAlgebra P r
    exact ha
  · intro A B _ _ hA hB
    exact (CyclicAlgebra P r).add_mem hA hB
  · intro A B _ _ hA hB
    exact (CyclicAlgebra P r).mul_mem hA hB
  · exact hM
noncomputable def cartwrightStegerOrderToCyclicAlgebra
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrder P r →+* CyclicAlgebra P r where
  toFun x := ⟨x.1, cartwrightStegerOrder_le_cyclicAlgebra P r x.1 x.2⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
private theorem globalBuildingOrderToCyclicApply
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    cartwrightStegerOrderToCyclicAlgebra P r x =
      (⟨x.val, cartwrightStegerOrder_le_cyclicAlgebra P r x.val x.property⟩ :
        CyclicAlgebra P r) := rfl
set_option maxHeartbeats 800000 in
@[simp] theorem cartwrightStegerOrderToCyclicAlgebra_coe
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r) :
    (cartwrightStegerOrderToCyclicAlgebra P r x :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = x.1 :=
  by
  exact congrArg Subtype.val (globalBuildingOrderToCyclicApply P r x)
noncomputable def cartwrightStegerOrderToBuilding
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrder P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P) :=
  (cyclicAlgebraToBuilding P r).toRingHom.comp
    (cartwrightStegerOrderToCyclicAlgebra P r)
noncomputable def cartwrightStegerOrderUnitToBuildingGL
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Units.map (cartwrightStegerOrderToBuilding P r)
noncomputable def constantCyclicEmbedding
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →+* CyclicAlgebra P r where
  toFun := constantCyclicElement P r
  map_zero' := Subtype.ext (map_zero (constantMatrixEmbedding P r))
  map_one' := Subtype.ext (map_one (constantMatrixEmbedding P r))
  map_add' c d := Subtype.ext (map_add (constantMatrixEmbedding P r) c d)
  map_mul' c d := Subtype.ext (map_mul (constantMatrixEmbedding P r) c d)
noncomputable def constantCyclicUnitHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →* (CyclicAlgebra P r)ˣ :=
  Units.map (constantCyclicEmbedding P r)
noncomputable def cartwrightStegerBCyclicUnit
    (P : BasePrime) (r : Rank) : (CyclicAlgebra P r)ˣ where
  val := cartwrightStegerBCyclicElement P r
  inv := ⟨cartwrightStegerBInverseMatrix P r,
    cartwrightStegerOrder_le_cyclicAlgebra P r _
      (cartwrightStegerBInverseMatrix_mem_order P r)⟩
  val_inv := Subtype.ext (cartwrightStegerB_mul_inverse P r)
  inv_val := Subtype.ext (cartwrightStegerB_inverse_mul P r)
noncomputable def cartwrightStegerGeneratorCyclicUnit
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (CyclicAlgebra P r)ˣ :=
  constantCyclicUnitHom P r (constantClassRepresentative P r u) *
    cartwrightStegerBCyclicUnit P r *
      (constantCyclicUnitHom P r (constantClassRepresentative P r u))⁻¹
noncomputable def cyclicUnitToBuildingGL
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Units.map (cyclicAlgebraToBuilding P r).toRingHom
noncomputable def cyclicUnitToBuildingPGL
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk.comp (cyclicUnitToBuildingGL P r)
noncomputable def CyclicCartwrightStegerLattice
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  Subgroup.closure (Set.range (cartwrightStegerGeneratorCyclicUnit P r))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


