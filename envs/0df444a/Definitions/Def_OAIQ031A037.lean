-- Prove2me | Definitions.Def_OAIQ031A037
-- name    : OAIQ031A037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:00:46.515848+00:00
-- url     : https://prove2.me/theorems/0a06333e-dfce-445a-b561-01d75c4c93fb
-- title:
--   Definitions bundle OAIQ031A037 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 9 definitions, 2 instances and 11 theorems. The definitions and types are `OAI.ArExplicit.CoinducedModule.coordinateEquiv`, `OAI.ArExplicit.CoinducedModule.freeEquiv`, `OAI.ArExplicit.EnvelopingBimodule.rightEquiv`, `OAI.ArExplicit.ExternalTensor.moduleScalarCoordinates`, `OAI.ArExplicit.bimoduleEnvelopingLeftEquiv`, `OAI.ArExplicit.restrictCokernelEquiv`, `OAI.ArExplicit.restrictKernelEquiv`, `OAI.ArExplicit.tensorLeftRegularEquiv`, `OAI.ArExplicit.tensorRightRegularEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_TensorRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorRestriction.lean), [`AuslanderReiten_Homology_RestrictKernelCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/RestrictKernelCokernel.lean), [`AuslanderReiten_Modules_BimoduleEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/BimoduleEnveloping.lean), [`AuslanderReiten_Modules_CoinducedModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/CoinducedModule.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Tensor_EnvelopingBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBimodule.lean), [`AuslanderReiten_Tensor_ExternalTensorCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCoordinates.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A003`, `OAIQ031A005`, `OAIQ031A011`, `OAIQ031A016` and `OAIQ031A017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A055`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A011
import Definitions.Def_OAIQ031A016
import Definitions.Def_OAIQ031A017

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_RestrictKernelCokernel
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory

universe u

variable {R S : Type u} [Ring R] [Ring S] (j : R →+* S)
variable {M N : ModuleCat.{u} S} (f : M ⟶ N)

def restrictKernelEquiv :
    ((ModuleCat.restrictScalars j).obj (kernelObject f)) ≃ₗ[R]
      LinearMap.ker (((ModuleCat.restrictScalars j).map f).hom) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictCokernelEquiv :
    ((ModuleCat.restrictScalars j).obj (cokernelObject f)) ≃ₗ[R]
      (((ModuleCat.restrictScalars j).obj N) ⧸ LinearMap.range (((ModuleCat.restrictScalars j).map f).hom)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernel_restrict_projective
    [Module.Projective R ((ModuleCat.restrictScalars j).obj M)]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj N)]
    (hf : Function.Surjective f.hom) :
    Module.Projective R ((ModuleCat.restrictScalars j).obj (kernelObject f)) := by
  let := projective_kernel_of_surjective (((ModuleCat.restrictScalars j).map f).hom) hf
  exact Module.Projective.of_equiv (restrictKernelEquiv j f).symm

theorem kernel_restrict_finite
    [Module.Finite R ((ModuleCat.restrictScalars j).obj M)]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj N)]
    (hf : Function.Surjective f.hom) :
    Module.Finite R ((ModuleCat.restrictScalars j).obj (kernelObject f)) := by
  let := finite_kernel_of_surjective (((ModuleCat.restrictScalars j).map f).hom) hf
  exact Module.Finite.equiv (restrictKernelEquiv j f).symm

theorem cokernel_restrict_projective
    [Module.Injective R ((ModuleCat.restrictScalars j).obj M)]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj N)]
    (hf : Function.Injective f.hom) :
    Module.Projective R ((ModuleCat.restrictScalars j).obj (cokernelObject f)) := by
  let := projective_cokernel_of_injective (((ModuleCat.restrictScalars j).map f).hom) hf
  exact Module.Projective.of_equiv (restrictCokernelEquiv j f).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorRestriction
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable (k R S : Type u) [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def tensorLeftRegularEquiv :
    ((ModuleCat.restrictScalars (tensorLeftInclusion k R S)).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) ≃ₗ[R]
      R ⊗[k] S where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    change ((r ⊗ₜ[k] (1 : S)) * (show R ⊗[k] S from z)) = r • (show R ⊗[k] S from z)
    let x : R ⊗[k] S := z
    change (r ⊗ₜ[k] (1 : S)) * x = r • x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp [mul_add, smul_add, hx, hy]
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]

def tensorRightRegularEquiv :
    ((ModuleCat.restrictScalars (tensorRightInclusion k R S)).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) ≃ₗ[S]
      S ⊗[k] R where
  __ := (TensorProduct.comm k R S).toAddEquiv
  map_smul' s z := by
    let x : R ⊗[k] S := z
    change TensorProduct.comm k R S (((1 : R) ⊗ₜ[k] s) * x) =
      s • TensorProduct.comm k R S x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp [mul_add, smul_add, hx, hy]
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem tensorLeftRegular_projective :
    Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
  Module.Projective.of_equiv (tensorLeftRegularEquiv k R S).symm

theorem tensorRightRegular_projective :
    Module.Projective S ((ModuleCat.restrictScalars (tensorRightInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
  Module.Projective.of_equiv (tensorRightRegularEquiv k R S).symm

theorem tensorLeftRegular_finite [Module.Finite k S] :
    Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := by
  let : Module.Finite R (R ⊗[k] S) := Module.Finite.of_basis ((Module.finBasis k S).baseChange R)
  exact Module.Finite.equiv (tensorLeftRegularEquiv k R S).symm

theorem tensorRightRegular_finite [Module.Finite k R] :
    Module.Finite S ((ModuleCat.restrictScalars (tensorRightInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := by
  let : Module.Finite S (S ⊗[k] R) := Module.Finite.of_basis ((Module.finBasis k R).baseChange S)
  exact Module.Finite.equiv (tensorRightRegularEquiv k R S).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBimodule
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

namespace EnvelopingBimodule

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

def rightEquiv : EnvelopingBimodule k R M ≃ₗ[Rᵐᵒᵖ]
    ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj M) where
  __ := coordinates M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instProjectiveMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion [Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  Module.Projective.of_equiv (rightEquiv M).symm

instance instFiniteMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion [Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  Module.Finite.equiv (rightEquiv M).symm

end EnvelopingBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_BimoduleEnveloping
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M]
variable [SMulCommClass R Rᵐᵒᵖ M]

def bimoduleEnvelopingLeftEquiv :
    ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj
      (bimoduleEnvelopingObject k R M)) ≃ₗ[R] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • ((1 : Rᵐᵒᵖ) • (show M from x)) = a • (show M from x)
    rw [one_smul]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_CoinducedModule
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace CoinducedModule

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M]

variable [Module.Finite k M]

def coordinateEquiv : CoinducedModule k R M ≃ₗ[R]
    (Fin (Module.finrank k M) → Coinduced k R) where
  toFun f i := ⟨(LinearMap.proj i).comp (coefficients.toLinearMap.comp f.functional)⟩
  invFun g := ⟨coefficients.symm.toLinearMap.comp
    (LinearMap.pi fun i => (g i).functional)⟩
  left_inv f := by
    ext t
    exact coefficients.symm_apply_apply (f.functional t)
  right_inv g := by
    funext i
    apply Coinduced.ext
    apply LinearMap.ext
    intro t
    exact congrFun (coefficients.apply_symm_apply (fun j => (g j).functional t)) i
  map_add' f g := by funext i; apply Coinduced.ext; ext t; simp
  map_smul' r f := by funext i; apply Coinduced.ext; ext t; rfl

def freeEquiv [Module.Finite k R] (τ : FrobeniusTrace k R) :
    CoinducedModule k R M ≃ₗ[R] (Fin (Module.finrank k M) → R) :=
  coordinateEquiv.trans (LinearEquiv.piCongrRight fun _ => τ.leftEquiv.symm)

theorem finite [Module.Finite k R] (τ : FrobeniusTrace k R) :
    Module.Finite R (CoinducedModule k R M) := Module.Finite.equiv (freeEquiv τ).symm

theorem free [Module.Finite k R] (τ : FrobeniusTrace k R) :
    Module.Free R (CoinducedModule k R M) := Module.Free.of_equiv (freeEquiv τ).symm

theorem projective [Module.Finite k R] (τ : FrobeniusTrace k R) :
    Module.Projective R (CoinducedModule k R M) := by
  let := free (M := M) τ
  exact Module.Projective.of_free

end CoinducedModule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

theorem mulY_injective (n : ℕ) : Function.Injective (mulY k n) := by
  intro f g h
  ext i
  have hi := congrFun h i.castSucc
  simpa using hi

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCoordinates
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def moduleScalarCoordinates (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    moduleObject k A B M N ≃ₗ[k] (M ⊗[k] N) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change representation k A B M N (algebraMap k (A ⊗[k] B) a) x = a • (show M ⊗[k] N from x)
    rw [AlgHom.commutes]
    rfl

end ArExplicit.ExternalTensor

end

end OAI
end


