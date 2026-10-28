-- Prove2me | Definitions.Def_OAIQ031A069
-- name    : OAIQ031A069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:15:29.229089+00:00
-- url     : https://prove2.me/theorems/bbc21bac-29ef-4eb9-b45a-68517d15f40c
-- title:
--   Definitions bundle OAIQ031A069 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 5 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.scalarCoordinates`, `OAI.ArExplicit.BalancedTensor.mapRightEquiv`, `OAI.ArExplicit.BalancedTensor.nativeObjectIso`, `OAI.ArExplicit.BarBalanced.rawEval`, `OAI.ArExplicit.EnvelopingBimodule.tensorProdInv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedRaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedRaw.lean), [`AuslanderReiten_Bar_BarScalarCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarScalarCoordinates.lean), [`AuslanderReiten_Tensor_BalancedTensorFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorFunctor.lean), [`AuslanderReiten_Tensor_BalancedTensorMapEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorMapEquiv.lean), [`AuslanderReiten_Tensor_BalancedTensorNative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorNative.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedProduct.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A030`, `OAIQ031A045` and `OAIQ031A049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A083`, `OAIQ031A084` and `OAIQ031A086`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A030
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A049

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedRaw
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def rawEval : (n : ℕ) → (AbsoluteBar.object k R n ⊗[k] M) →ₗ[k] ModuleBar.object k R M n
  | 0 => TensorProduct.lift (Algebra.lsmul k k M).toLinearMap
  | n+1 => ((rawEval n).lTensor R).comp
      (TensorProduct.assoc k R (AbsoluteBar.object k R n) M).toLinearMap

@[simp] theorem rawEval_zero (a : R) (m : M) :
    rawEval k R M 0 (a ⊗ₜ[k] m) = a • m := rfl

@[simp] theorem rawEval_succ (n : ℕ) (a : R) (x : AbsoluteBar.object k R n) (m : M) :
    rawEval k R M (n+1) ((a ⊗ₜ[k] x) ⊗ₜ[k] m) =
      a ⊗ₜ[k] rawEval k R M n (x ⊗ₜ[k] m) := rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarScalarCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def scalarCoordinates (n : ℕ) : moduleObject k R n ≃ₗ[k] object k R n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change representation k R n (algebraMap k (Enveloping k R) a)
      (show object k R n from x) = a • (show object k R n from x)
    rw [AlgHom.commutes]
    rfl

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

variable {k R S F M N L : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]

theorem mapRight_surjective (b : M →ₗ[R] N) (hb : Function.Surjective b) :
    Function.Surjective (mapRight (k := k) (F := F) (S := S) b) := by
  intro z
  induction z using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul f n =>
    obtain ⟨m, rfl⟩ := hb n
    exact ⟨tmul f m, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ x y⟩

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorMapEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
variable {k R S F L M : Type*} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

def mapRightEquiv (e : L ≃ₗ[R] M) : BalancedTensor k R F L ≃ₗ[S] BalancedTensor k R F M where
  __ := mapRight (k := k) (F := F) (S := S) e.toLinearMap
  invFun := mapRight (k := k) (F := F) (S := S) e.symm.toLinearMap
  left_inv x := by
    change mapRight (k := k) (F := F) (S := S) e.symm.toLinearMap
      (mapRight (k := k) (F := F) (S := S) e.toLinearMap x) = x
    have h := congrArg (fun t : BalancedTensor k R F L →ₗ[S] BalancedTensor k R F L => t x)
      (mapRight_comp (k := k) (F := F) (S := S) e.toLinearMap e.symm.toLinearMap)
    simpa only [e.symm_comp, mapRight_id, LinearMap.comp_apply, LinearMap.id_apply] using h.symm
  right_inv x := by
    change mapRight (k := k) (F := F) (S := S) e.toLinearMap
      (mapRight (k := k) (F := F) (S := S) e.symm.toLinearMap x) = x
    have h := congrArg (fun t : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F M => t x)
      (mapRight_comp (k := k) (F := F) (S := S) e.symm.toLinearMap e.toLinearMap)
    simpa only [e.comp_symm, mapRight_id, LinearMap.comp_apply, LinearMap.id_apply] using h.symm

@[simp] theorem mapRightEquiv_tmul (e : L ≃ₗ[R] M) (f : F) (x : L) :
    mapRightEquiv (k := k) (F := F) (S := S) e (tmul f x) = tmul f (e x) := rfl

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorNative
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.BalancedTensor
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable (M : Type u) [AddCommGroup M] [Module R M] [mM : Module k M] [IsScalarTower k R M]

theorem nativeObject_eq :
    (functor (k := k) (R := R) (S := S) (F := F)).obj (ModuleCat.of R M) =
      ModuleCat.of S (BalancedTensor k R F M) := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  rfl

def nativeObjectIso :
    (functor (k := k) (R := R) (S := S) (F := F)).obj (ModuleCat.of R M) ≅
      ModuleCat.of S (BalancedTensor k R F M) :=
  eqToIso (nativeObject_eq (k := k) (R := R) (S := S) (F := F) M)

theorem nativeObjectIso_tmul (f : F) (m : M) :
    (nativeObjectIso (k := k) (R := R) (S := S) (F := F) M).hom.hom
      (letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
       tmul f m) = tmul f m := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  rfl

variable {M}
variable {L : Type u} [AddCommGroup L] [Module R L] [mL : Module k L] [IsScalarTower k R L]

theorem nativeObjectIso_natural (f : M →ₗ[R] L) :
    (functor (k := k) (R := R) (S := S) (F := F)).map (ModuleCat.ofHom f) ≫
        (nativeObjectIso (k := k) (R := R) (S := S) (F := F) L).hom =
      (nativeObjectIso (k := k) (R := R) (S := S) (F := F) M).hom ≫
        ModuleCat.ofHom (mapRight (k := k) (F := F) (S := S) f) := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  cases ExternalTensor.canonicalScalar_eq k R L (mM := mL)
  rfl

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedProduct
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
  [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
  [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable (X : ModuleCat.{u} R) [Module k X]
local notation "ProdMN" => ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N)
local notation "EM" => BalancedTensor k R (EnvelopingBimodule k R M) X
local notation "EN" => BalancedTensor k R (EnvelopingBimodule k R N) X
local notation "EP" => BalancedTensor k R (EnvelopingBimodule k R ProdMN) X

def tensorProdInv : (EM × EN) →ₗ[R] EP :=
  (tensorMap (k := k) X (ModuleCat.ofHom (X := M) (Y := ProdMN) (LinearMap.inl (R ⊗[k] Rᵐᵒᵖ) M N))).coprod
    (tensorMap (k := k) X (ModuleCat.ofHom (X := N) (Y := ProdMN) (LinearMap.inr (R ⊗[k] Rᵐᵒᵖ) M N)))

end ArExplicit.EnvelopingBimodule

end

end OAI
end


