-- Prove2me | solution 1 for Algebra.TensorProduct.map_norm_eq_norm_map_of_rightAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3ac9b3d7-6449-5925-8797-1694e4dc5ee1

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra

set_option autoImplicit false

open scoped TensorProduct

namespace NBCAux

open scoped TensorProduct.RightActions

variable {K L B : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem repr_tmul (b : Module.Basis n K L) (l : L) (x : B) (i : n) :
    (b.rightBaseChange L (B := B)).repr (l ⊗ₜ[K] x) i = b.repr l i • x := by
  classical
  conv_lhs => rw [← b.sum_repr l]
  simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Module.Basis.rightBaseChange_repr, Finsupp.single_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk)]
  · rw [if_pos rfl]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end NBCAux

namespace NBCAux2

open scoped TensorProduct.RightActions

variable {K L E F : Type*} [Field K] [Field L] [Algebra K L] [Field E] [Algebra K E] [Field F] [Algebra K F]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem repr_map (b : Module.Basis n K L) (φ : E →ₐ[K] F) (y : L ⊗[K] E) (i : n) :
    (b.rightBaseChange L (B := F)).repr (Algebra.TensorProduct.map (AlgHom.id K L) φ y) i =
      φ ((b.rightBaseChange L (B := E)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul l e =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, NBCAux.repr_tmul, NBCAux.repr_tmul, Algebra.smul_def,
        Algebra.smul_def, map_mul, φ.commutes]
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]

end NBCAux2

open scoped TensorProduct.RightActions in

theorem solution
    (K L E F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field E] [Algebra K E] [Field F] [Algebra K F] (ι : E →ₐ[K] F) (x : L ⊗[K] E) :
    ι (Algebra.norm E x) =
      Algebra.norm F (Algebra.TensorProduct.map (AlgHom.id K L) ι x) := by
  classical
  let b := Module.finBasis K L
  rw [Algebra.norm_eq_matrix_det (b.rightBaseChange L (B := E)) x,
    Algebra.norm_eq_matrix_det (b.rightBaseChange L (B := F)), AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.rightBaseChange_apply, Module.Basis.rightBaseChange_apply]
  have hm : Algebra.TensorProduct.map (AlgHom.id K L) ι x * b j ⊗ₜ[K] (1 : F)
      = Algebra.TensorProduct.map (AlgHom.id K L) ι (x * b j ⊗ₜ[K] (1 : E)) := by
    rw [map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  rw [hm, NBCAux2.repr_map]

end S_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra
end P2MW
export P2MW.S_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra (solution)
