-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NativeTensorSumOperators_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_NativeTensorSumOperators_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:07:51.559934+00:00
-- url     : https://prove2.me/theorems/c1b51785-c3df-4ef6-a491-07b94494a528
-- title:
--   Native Tensor Sum Operators — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for native tensor sum operators used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_NativeTensorSumOperators.lean, selected declarations in lines 18–95; source SHA-256 23ab125a42607cc80c17ad5a18e32260c34da1fdd488f0ff2dfa229dc7f01884; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NativePolynomialTensor_SixOne20261024_Defs
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

noncomputable def nativeTensorSumModule : ModuleCat.{u} (MvPolynomial W k) :=
  ModuleCat.of (MvPolynomial W k) (DirectSum I (fun i => nativePolynomialField k W (B i) ⊗[k] P i))

noncomputable def nativeTensorSumField : ModuleCat.{u} k :=
  ModuleCat.of k (DirectSum I (fun i => nativePolynomialField k W (B i) ⊗[k] P i))

noncomputable def nativeTensorSumFieldIso :
    nativePolynomialField k W (nativeTensorSumModule k W B P) ≅ nativeTensorSumField k W B P := by
  let e : nativePolynomialField k W (nativeTensorSumModule k W B P) ≃ₗ[k] nativeTensorSumField k W B P := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact e.toModuleIso

noncomputable def nativeTensorSumMap (f : ∀ i, B i ⟶ C i) :
    nativeTensorSumModule k W B P ⟶ nativeTensorSumModule k W C P :=
  ModuleCat.ofHom (R := MvPolynomial W k)
    (X := nativeTensorSumModule k W B P) (Y := nativeTensorSumModule k W C P)
    (DirectSum.toModule (MvPolynomial W k) I (nativeTensorSumModule k W C P)
      (fun i => (DirectSum.lof (MvPolynomial W k) I
        (fun j => nativePolynomialField k W (C j) ⊗[k] P j) i).comp
          (nativePolynomialTensorMap k W (B i) (C i) (f i) (P i))))

noncomputable def nativeTensorSumFieldMap (f : ∀ i, B i ⟶ C i) :
    nativeTensorSumField k W B P ⟶ nativeTensorSumField k W C P :=
  (nativeTensorSumFieldIso k W B P).inv ≫
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map
      (nativeTensorSumMap k W B C P f) ≫ (nativeTensorSumFieldIso k W C P).hom

theorem nativeTensorSumFieldMap_lof_tmul (f : ∀ i, B i ⟶ C i)
    (i : I) (x : nativePolynomialField k W (B i)) (y : P i) :
    nativeTensorSumFieldMap k W B C P f
      (DirectSum.lof k I (fun i => nativePolynomialField k W (B i) ⊗[k] P i) i (x ⊗ₜ[k] y)) =
      DirectSum.lof k I (fun i => nativePolynomialField k W (C i) ⊗[k] P i) i
        ((show nativePolynomialField k W (C i) from f i x) ⊗ₜ[k] y) := by
  change DirectSum.toModule (MvPolynomial W k) I (nativeTensorSumModule k W C P)
    (fun i => (DirectSum.lof (MvPolynomial W k) I
      (fun j => nativePolynomialField k W (C j) ⊗[k] P j) i).comp
        (nativePolynomialTensorMap k W (B i) (C i) (f i) (P i)))
    (DirectSum.lof (MvPolynomial W k) I (fun i => nativePolynomialField k W (B i) ⊗[k] P i) i
      (x ⊗ₜ[k] y)) = _
  rw [DirectSum.toModule_lof]
  exact congrArg (DirectSum.lof (MvPolynomial W k) I
    (fun i => nativePolynomialField k W (C i) ⊗[k] P i) i)
    (nativePolynomialTensorMap_tmul k W (B i) (C i) (f i) (P i) x y)

theorem nativeTensorSumFieldIso_map (f : ∀ i, B i ⟶ C i) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map
      (nativeTensorSumMap k W B C P f) ≫ (nativeTensorSumFieldIso k W C P).hom =
      (nativeTensorSumFieldIso k W B P).hom ≫ nativeTensorSumFieldMap k W B C P f := by
  simp only [nativeTensorSumFieldMap, Iso.hom_inv_id_assoc]

noncomputable def nativeTensorSumFieldScalar (s : MvPolynomial W k) :
    nativeTensorSumField k W B P ⟶ nativeTensorSumField k W B P :=
  (nativeTensorSumFieldIso k W B P).inv ≫
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map
      (ModuleCat.ofHom (R := MvPolynomial W k) (X := nativeTensorSumModule k W B P)
        (Y := nativeTensorSumModule k W B P) (LinearMap.lsmul (MvPolynomial W k) _ s)) ≫
    (nativeTensorSumFieldIso k W B P).hom

theorem nativeTensorSumFieldScalar_lof_tmul (s : MvPolynomial W k)
    (i : I) (x : nativePolynomialField k W (B i)) (y : P i) :
    nativeTensorSumFieldScalar k W B P s
      (DirectSum.lof k I (fun i => nativePolynomialField k W (B i) ⊗[k] P i) i (x ⊗ₜ[k] y)) =
      DirectSum.lof k I (fun i => nativePolynomialField k W (B i) ⊗[k] P i) i
        ((s • x) ⊗ₜ[k] y) := by
  change s • DFinsupp.single (β := fun j => nativePolynomialField k W (B j) ⊗[k] P j) i (x ⊗ₜ[k] y) =
    DFinsupp.single (β := fun j => nativePolynomialField k W (B j) ⊗[k] P j) i ((s • x) ⊗ₜ[k] y)
  rw [← DFinsupp.single_smul, TensorProduct.smul_tmul']

theorem nativeTensorSumFieldIso_variable (j : W) :
    polynomialVariableFieldHom k W (nativeTensorSumModule k W B P) j ≫
        (nativeTensorSumFieldIso k W B P).hom =
      (nativeTensorSumFieldIso k W B P).hom ≫ nativeTensorSumFieldScalar k W B P (MvPolynomial.X j) := by
  simp only [nativeTensorSumFieldScalar, polynomialVariableFieldHom, Iso.hom_inv_id_assoc]

end LPCA


