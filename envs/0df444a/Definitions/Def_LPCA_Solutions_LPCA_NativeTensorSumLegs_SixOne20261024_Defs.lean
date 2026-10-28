-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NativeTensorSumLegs_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_NativeTensorSumLegs_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:08:17.754256+00:00
-- url     : https://prove2.me/theorems/c058e543-458a-435d-b48d-aee53587840d
-- title:
--   Native Tensor Sum Legs — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for native tensor sum legs used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_NativeTensorSumLegs.lean, selected declarations in lines 17–58; source SHA-256 897b3c8e81811c2f6af3f6570841cc5fdce53b806a18f4e3f3b8c970e95fbbaf; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativePolynomialTensor_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativeTensorSumOperators_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory TensorProduct

universe u

variable (k W : Type u) [CommRing k]
variable {I : Type u} [DecidableEq I]
variable (B C : I → ModuleCat.{u} (MvPolynomial W k)) (P : I → ModuleCat.{u} k)

noncomputable def nativeTensorSumLeg (i : I) (A : ModuleCat.{u} k)
    (f : A ⟶ nativePolynomialField k W (B i)) (m : P i) : A ⟶ nativeTensorSumField k W B P :=
  ModuleCat.ofHom (R := k) (X := A) (Y := nativeTensorSumField k W B P)
    ((DirectSum.lof k I (fun j => nativePolynomialField k W (B j) ⊗[k] P j) i).comp
      (((TensorProduct.mk k (nativePolynomialField k W (B i)) (P i)).flip m).comp f.hom))



theorem nativeTensorSumLeg_map (f : ∀ i, B i ⟶ C i) (i : I)
    (A H : ModuleCat.{u} k) (a : A ⟶ nativePolynomialField k W (B i))
    (b : H ⟶ nativePolynomialField k W (C i)) (v : A ⟶ H) (m : P i)
    (h : a ≫ (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map (f i) = v ≫ b) :
    nativeTensorSumLeg k W B P i A a m ≫ nativeTensorSumFieldMap k W B C P f =
      v ≫ nativeTensorSumLeg k W C P i H b m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change nativeTensorSumFieldMap k W B C P f
    (DirectSum.lof k I (fun j => nativePolynomialField k W (B j) ⊗[k] P j) i (a x ⊗ₜ[k] m)) = _
  rw [nativeTensorSumFieldMap_lof_tmul]
  exact congrArg (fun y : nativePolynomialField k W (C i) =>
    DirectSum.lof k I (fun j => nativePolynomialField k W (C j) ⊗[k] P j) i (y ⊗ₜ[k] m))
      (moduleSquare_apply k _ _ _ _ _ _ _ _ h x)

theorem nativeTensorSumLeg_variable (i : I) (j : W)
    (A H : ModuleCat.{u} k) (a : A ⟶ nativePolynomialField k W (B i))
    (b : H ⟶ nativePolynomialField k W (B i)) (v : A ⟶ H) (m : P i)
    (h : a ≫ polynomialVariableFieldHom k W (B i) j = v ≫ b) :
    nativeTensorSumLeg k W B P i A a m ≫ nativeTensorSumFieldScalar k W B P (MvPolynomial.X j) =
      v ≫ nativeTensorSumLeg k W B P i H b m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change nativeTensorSumFieldScalar k W B P (MvPolynomial.X j)
    (DirectSum.lof k I (fun j => nativePolynomialField k W (B j) ⊗[k] P j) i (a x ⊗ₜ[k] m)) = _
  rw [nativeTensorSumFieldScalar_lof_tmul]
  exact congrArg (fun y : nativePolynomialField k W (B i) =>
    DirectSum.lof k I (fun j => nativePolynomialField k W (B j) ⊗[k] P j) i (y ⊗ₜ[k] m))
      (moduleSquare_apply k _ _ _ _ _ _ _ _ h x)

end LPCA


