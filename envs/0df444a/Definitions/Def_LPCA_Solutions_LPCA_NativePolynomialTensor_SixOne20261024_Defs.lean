-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NativePolynomialTensor_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_NativePolynomialTensor_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:07:24.35651+00:00
-- url     : https://prove2.me/theorems/d7d56095-86a0-4531-a893-38cd9dd46da7
-- title:
--   Native Polynomial Tensor — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for native polynomial tensor used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Explicit constant restriction retains the given native polynomial action.
--
--   Tensor a native polynomial map with the identity over the constants.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_NativePolynomialTensor.lean, selected declarations in lines 16–50; source SHA-256 26698056369d11555e4db72ed7df948112dd976ce2334b92bbc165272fab148b; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory TensorProduct

universe u

variable (k W : Type u) [CommRing k]

/-- Explicit constant restriction retains the given native polynomial action. -/
noncomputable abbrev nativePolynomialField (M : ModuleCat.{u} (MvPolynomial W k)) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M

instance nativePolynomialFieldScalarTower (M : ModuleCat.{u} (MvPolynomial W k)) :
    IsScalarTower k (MvPolynomial W k) (nativePolynomialField k W M) where
  smul_assoc c p x := by
    change (c • p) • (show M from x) = (MvPolynomial.C c : MvPolynomial W k) • (p • x)
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

/-- Tensor a native polynomial map with the identity over the constants. -/
noncomputable def nativePolynomialTensorMap (M N : ModuleCat.{u} (MvPolynomial W k))
    (f : M ⟶ N) (P : ModuleCat.{u} k) :
    nativePolynomialField k W M ⊗[k] P →ₗ[MvPolynomial W k] nativePolynomialField k W N ⊗[k] P :=
  TensorProduct.AlgebraTensorModule.map
    (M := nativePolynomialField k W M) (P := nativePolynomialField k W N) f.hom LinearMap.id

theorem nativePolynomialTensorMap_tmul (M N : ModuleCat.{u} (MvPolynomial W k))
    (f : M ⟶ N) (P : ModuleCat.{u} k) (x : nativePolynomialField k W M) (y : P) :
    nativePolynomialTensorMap k W M N f P (x ⊗ₜ[k] y) =
      (show nativePolynomialField k W N from f x) ⊗ₜ[k] y := by
  exact TensorProduct.AlgebraTensorModule.map_tmul
    (M := nativePolynomialField k W M) (P := nativePolynomialField k W N) f.hom LinearMap.id x y

theorem nativePolynomialTensorMap_square (M N H : ModuleCat.{u} (MvPolynomial W k))
    (f : M ⟶ N) (g : N ⟶ H) (P : ModuleCat.{u} k) (h : f ≫ g = 0) :
    (nativePolynomialTensorMap k W N H g P).comp (nativePolynomialTensorMap k W M N f P) = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  simp only [LinearMap.comp_apply, nativePolynomialTensorMap_tmul, LinearMap.zero_apply]
  have hs : g (f x) = 0 := by
    have he := moduleSquare_apply (MvPolynomial W k) M N M H f g (𝟙 M) 0 (by simpa using h) x
    exact he
  rw [hs, TensorProduct.zero_tmul]

end LPCA


