-- Prove2me | Definitions.Def_Operator_Dilation_Halmos
-- name    : Operator_Dilation_Halmos
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:26.203235+00:00
-- url     : https://prove2.me/theorems/f5e2a1b9-b83e-4d14-9c8e-628eec47662c
-- title:
--   Halmos
-- statement:
--   Definitions and structural lemmas for Halmos, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Halmos.lean

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
noncomputable def halmosOffDiagonalLinear (T : E →L[ℂ] E) :
    WithLp 2 (E × E) →ₗ[ℂ] WithLp 2 (E × E) where
  toFun x := WithLp.toLp 2 (T x.snd, adjoint T x.fst)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    change (T (x.snd + y.snd), adjoint T (x.fst + y.fst)) =
      (T x.snd + T y.snd, adjoint T x.fst + adjoint T y.fst)
    exact Prod.ext (map_add T x.snd y.snd) (map_add (adjoint T) x.fst y.fst)
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    change (T (c • x.snd), adjoint T (c • x.fst)) =
      (c • T x.snd, c • adjoint T x.fst)
    exact Prod.ext (map_smul T c x.snd) (map_smul (adjoint T) c x.fst)
theorem halmosOffDiagonalLinear_bound (T : E →L[ℂ] E)
    (x : WithLp 2 (E × E)) :
    ‖halmosOffDiagonalLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg x))).mp
  calc
    ‖halmosOffDiagonalLinear T x‖ ^ 2 = ‖T x.snd‖ ^ 2 + ‖adjoint T x.fst‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      rfl
    _ ≤ (‖T‖ * ‖x.snd‖) ^ 2 + (‖T‖ * ‖x.fst‖) ^ 2 := by
      exact add_le_add
        (pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x.snd) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (by
          simpa only [LinearIsometryEquiv.norm_map] using (adjoint T).le_opNorm x.fst) 2)
    _ = ‖T‖ ^ 2 * (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by ring
    _ = ‖T‖ ^ 2 * ‖x‖ ^ 2 := by rw [WithLp.prod_norm_sq_eq_of_L2]
    _ = (‖T‖ * ‖x‖) ^ 2 := by ring
noncomputable def halmosOffDiagonal (T : E →L[ℂ] E) :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) :=
  (halmosOffDiagonalLinear T).mkContinuous ‖T‖ (halmosOffDiagonalLinear_bound T)
noncomputable def halmosGrading :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℂ E) (LinearIsometryEquiv.neg ℂ (E := E)) :
      WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E))
noncomputable def halmosFlip :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) :=
  LinearIsometryEquiv.withLpProdComm 2 ℂ E E


