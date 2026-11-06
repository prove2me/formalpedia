-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:23:59.364215+00:00
-- url     : https://prove2.me/theorems/d3512534-695d-40ed-b090-496010cea387
-- title:
--   Principal Shift
-- statement:
--   Definitions and structural lemmas for Principal Shift, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PrincipalShift.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
namespace GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
omit [Algebra k[X] F] [Algebra k⟮X⟯ F]
  [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
/-- For a nonzero function, membership in the all-place Riemann--Roch
submodule is exactly coefficientwise nonnegativity of its principal divisor
plus the prescribed divisor. -/
theorem mem_riemannRochSubmodule_iff_order_add_nonnegative
    (G : Divisor (GlobalPlace k F)) {f : F} (hf : f ≠ 0) :
    f ∈ riemannRochSubmodule G ↔
      ∀ P : GlobalPlace k F, 0 ≤ P.order f + G P := by
  rw [mem_riemannRochSubmodule_iff]
  constructor
  · intro h P
    have hlog : WithZero.log (P.valuation f) ≤ G P :=
      (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf)).mpr (h P)
    change 0 ≤ -WithZero.log (P.valuation f) + G P
    omega
  · intro h P
    apply (WithZero.log_le_iff_le_exp
      ((P.valuation).ne_zero_iff.mpr hf)).mp
    have hP := h P
    change 0 ≤ -WithZero.log (P.valuation f) + G P at hP
    omega
noncomputable def riemannRochSubmodule_principal_add_equiv
    (u : Fˣ) (G : Divisor (GlobalPlace k F)) :
    riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) ≃ₗ[k]
      riemannRochSubmodule G where
  toFun x := ⟨(u : F) * (x : F), by
    by_cases hx : (x : F) = 0
    · simpa only [hx, mul_zero] using (riemannRochSubmodule G).zero_mem
    · apply (mem_riemannRochSubmodule_iff_order_add_nonnegative G
        (mul_ne_zero u.ne_zero hx)).mpr
      have hxOrder :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative
          (GlobalPlace.principalDivisor (k := k) (F := F) u + G) hx).mp x.property
      intro P
      have hP := hxOrder P
      rw [Finsupp.add_apply, GlobalPlace.principalDivisor_apply] at hP
      rw [GlobalPlace.order_mul P u.ne_zero hx]
      omega⟩
  invFun x := ⟨((u⁻¹ : Fˣ) : F) * (x : F), by
    by_cases hx : (x : F) = 0
    · simpa only [hx, mul_zero] using
        (riemannRochSubmodule
          (GlobalPlace.principalDivisor (k := k) (F := F) u + G)).zero_mem
    · apply (mem_riemannRochSubmodule_iff_order_add_nonnegative
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G)
        (mul_ne_zero (Units.ne_zero _) hx)).mpr
      have hxOrder :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp x.property
      intro P
      have hP := hxOrder P
      rw [GlobalPlace.order_mul P (Units.ne_zero _) hx,
        show P.order ((u⁻¹ : Fˣ) : F) = -P.order (u : F) by
          simpa only [Units.val_inv_eq_inv_val] using
            (GlobalPlace.order_inv P (u : F)),
        Finsupp.add_apply, GlobalPlace.principalDivisor_apply]
      omega⟩
  left_inv x := by
    apply Subtype.ext
    change ((u⁻¹ : Fˣ) : F) * ((u : F) * (x : F)) = (x : F)
    simp
  right_inv x := by
    apply Subtype.ext
    change (u : F) * (((u⁻¹ : Fˣ) : F) * (x : F)) = (x : F)
    simp
  map_add' x y := by
    apply Subtype.ext
    change (u : F) * ((x : F) + (y : F)) =
      (u : F) * (x : F) + (u : F) * (y : F)
    exact mul_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    change (u : F) * (c • (x : F)) = c • ((u : F) * (x : F))
    simp only [Algebra.smul_def]
    ring
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


