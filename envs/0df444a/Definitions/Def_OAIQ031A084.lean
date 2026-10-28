-- Prove2me | Definitions.Def_OAIQ031A084
-- name    : OAIQ031A084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:25:45.479989+00:00
-- url     : https://prove2.me/theorems/39cbff44-c250-4fe4-8d01-9b1d06806e7c
-- title:
--   Definitions bundle OAIQ031A084 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 9 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.tensorEvaluationIso`, `OAI.ArExplicit.BarBalanced.cons`, `OAI.ArExplicit.BarBalanced.coordinates`, `OAI.ArExplicit.BarBalanced.embedding`, `OAI.ArExplicit.BarBalanced.evalBilinear`, `OAI.ArExplicit.BarBalanced.evaluated`, `OAI.ArExplicit.BarBalanced.evaluation`, `OAI.ArExplicit.BarBalanced.prepend`, `OAI.ArExplicit.BarBalanced.prependBalanced`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedEquiv.lean), [`AuslanderReiten_Bar_BarBalancedModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedModule.lean), [`AuslanderReiten_Bar_BarBalancedRaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedRaw.lean), [`AuslanderReiten_Tensor_BalancedTensorFunctorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorFunctorExt.lean), [`AuslanderReiten_Tensor_BalancedTensorNativeEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorNativeEvaluation.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A063`, `OAIQ031A065`, `OAIQ031A066` and `OAIQ031A069` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A097` and `OAIQ031A098`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A065
import Definitions.Def_OAIQ031A066
import Definitions.Def_OAIQ031A069

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedRaw
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem rawEval_right (n : ℕ) (a : Rᵐᵒᵖ) (x : AbsoluteBar.object k R n) (m : M) :
    rawEval k R M n ((AbsoluteBar.right k R n a x) ⊗ₜ[k] m) =
      rawEval k R M n (x ⊗ₜ[k] (MulOpposite.unop a • m)) := by
  induction n with
  | zero => exact mul_smul x (MulOpposite.unop a) m
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul b x =>
      rw [AbsoluteBar.right_tmul, rawEval_succ, rawEval_succ, ih]

theorem rawEval_left (n : ℕ) (a : R) (x : AbsoluteBar.object k R n) (m : M) :
    rawEval k R M n ((AbsoluteBar.left k R n a x) ⊗ₜ[k] m) =
      ModuleBar.left k R M n a (rawEval k R M n (x ⊗ₜ[k] m)) := by
  cases n with
  | zero => exact mul_smul a x m
  | succ n =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul b x => rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

abbrev evaluated (n : ℕ) := BalancedTensor k R (bar k R n) M

def coordinates (n : ℕ) : bar k R n ≃ₗ[k] AbsoluteBar.object k R n :=
  EnvelopingBimodule.scalarEquiv (AbsoluteBar.moduleObject k R n)

theorem coordinates_left (n : ℕ) (a : R) (x : bar k R n) :
    coordinates k R n (a • x) = AbsoluteBar.left k R n a (coordinates k R n x) := by
  change AbsoluteBar.left k R n a (AbsoluteBar.right k R n 1 x.value) =
    AbsoluteBar.left k R n a x.value
  rw [map_one]
  rfl

theorem coordinates_right (n : ℕ) (a : Rᵐᵒᵖ) (x : bar k R n) :
    coordinates k R n (a • x) = AbsoluteBar.right k R n a (coordinates k R n x) := by
  change AbsoluteBar.left k R n 1 (AbsoluteBar.right k R n a x.value) =
    AbsoluteBar.right k R n a x.value
  exact AbsoluteBar.left_one k R n _

def evalBilinear (n : ℕ) : bar k R n →ₗ[k] M →ₗ[k] ModuleBar.moduleObject k R M n where
  toFun x := (rawEval k R M n).comp (TensorProduct.mk k (AbsoluteBar.object k R n) M
    (coordinates k R n x))
  map_add' x y := by
    ext m
    change rawEval k R M n (coordinates k R n (x+y) ⊗ₜ[k] m) =
      rawEval k R M n (coordinates k R n x ⊗ₜ[k] m) + rawEval k R M n (coordinates k R n y ⊗ₜ[k] m)
    rw [map_add, TensorProduct.add_tmul, map_add]
  map_smul' a x := by
    ext m
    change rawEval k R M n (coordinates k R n (a • x) ⊗ₜ[k] m) =
      a • rawEval k R M n (coordinates k R n x ⊗ₜ[k] m)
    rw [map_smul]
    exact (congrArg (rawEval k R M n)
      (TensorProduct.smul_tmul' a (coordinates k R n x) m).symm).trans
      ((rawEval k R M n).map_smul a (coordinates k R n x ⊗ₜ[k] m))

@[simp] theorem evalBilinear_apply (n : ℕ) (x : bar k R n) (m : M) :
    evalBilinear k R M n x m = rawEval k R M n ((coordinates k R n x) ⊗ₜ[k] m) := rfl

theorem evalBilinear_balance (n : ℕ) (x : bar k R n) (a : R) (m : M) :
    evalBilinear k R M n (MulOpposite.op a • x) m = evalBilinear k R M n x (a • m) := by
  rw [evalBilinear_apply, coordinates_right, evalBilinear_apply]
  exact rawEval_right k R M n (MulOpposite.op a) _ m

theorem evalBilinear_left (n : ℕ) (a : R) (x : bar k R n) (m : M) :
    evalBilinear k R M n (a • x) m = a • evalBilinear k R M n x m := by
  rw [evalBilinear_apply, coordinates_left]
  exact rawEval_left k R M n a _ m

def evaluation (n : ℕ) : evaluated k R M n →ₗ[R] ModuleBar.moduleObject k R M n :=
  BalancedTensor.liftLeft (evalBilinear k R M n) (evalBilinear_balance k R M n)
    (evalBilinear_left k R M n)

@[simp] theorem evaluation_tmul (n : ℕ) (x : bar k R n) (m : M) :
    evaluation k R M n (BalancedTensor.tmul x m) =
      rawEval k R M n ((coordinates k R n x) ⊗ₜ[k] m) := rfl

def prepend (n : ℕ) (a : R) : bar k R n →ₗ[k] bar k R (n+1) :=
  (coordinates k R (n+1)).symm.toLinearMap.comp
    ((TensorProduct.mk k R (AbsoluteBar.object k R n) a).comp
      (coordinates k R n).toLinearMap)

@[simp] theorem coordinates_prepend (n : ℕ) (a : R) (x : bar k R n) :
    coordinates k R (n+1) (prepend k R n a x) = a ⊗ₜ[k] coordinates k R n x :=
  (coordinates k R (n+1)).apply_symm_apply _

theorem prepend_right (n : ℕ) (a : R) (b : Rᵐᵒᵖ) (x : bar k R n) :
    prepend k R n a (b • x) = b • prepend k R n a x := by
  apply (coordinates k R (n+1)).injective
  rw [coordinates_prepend, coordinates_right, coordinates_right,
    coordinates_prepend, AbsoluteBar.right_tmul]

def prependBalanced (n : ℕ) (a : R) : evaluated k R M n →ₗ[k] evaluated k R M (n+1) :=
  BalancedTensor.map (prepend k R n a) LinearMap.id (prepend_right k R n a) (by intros; rfl)

omit [IsScalarTower k R M] in
@[simp] theorem prependBalanced_tmul (n : ℕ) (a : R) (x : bar k R n) (m : M) :
    prependBalanced k R M n a (BalancedTensor.tmul x m) =
      BalancedTensor.tmul (prepend k R n a x) m := rfl

def cons (n : ℕ) : R →ₗ[k] evaluated k R M n →ₗ[k] evaluated k R M (n+1) where
  toFun := prependBalanced k R M n
  map_add' a b := by
    apply BalancedTensor.hom_ext
    intro x m
    simp only [LinearMap.add_apply, prependBalanced_tmul]
    rw [← BalancedTensor.add_tmul (k := k) (R := R)]
    congr 1
    apply (coordinates k R (n+1)).injective
    rw [map_add, coordinates_prepend k R n (a+b) x,
      coordinates_prepend k R n a x, coordinates_prepend k R n b x, TensorProduct.add_tmul]
  map_smul' c a := by
    apply BalancedTensor.hom_ext
    intro x m
    simp only [RingHom.id_apply, LinearMap.smul_apply, prependBalanced_tmul]
    rw [← BalancedTensor.scalar_tmul (k := k) (R := R)]
    congr 1

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

def embedding : (n : ℕ) → ModuleBar.object k R M n →ₗ[k] evaluated k R M n
  | 0 => BalancedTensor.mk ((coordinates k R 0).symm 1)
  | n+1 => TensorProduct.lift ((LinearMap.lcomp k _ (embedding n)).comp (cons k R M n))

omit [IsScalarTower k R M] in
@[simp] theorem embedding_succ (n : ℕ) (a : R) (x : ModuleBar.object k R M n) :
    embedding k R M (n+1) (a ⊗ₜ[k] x) =
      prependBalanced k R M n a (embedding k R M n x) := rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorNativeEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {N : ModuleCat.{u} S} (e : BalancedTensor k R F M ≃ₗ[S] N)

def tensorEvaluationIso :
    (functor (k := k) (R := R) (S := S) (F := F)).obj (ModuleCat.of R M) ≅ N :=
  nativeObjectIso (k := k) (R := R) (S := S) (F := F) M ≪≫ e.toModuleIso

theorem tensorEvaluationIso_tmul (f : F) (m : M) :
    (tensorEvaluationIso M e).hom.hom
      (letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
       tmul f m) = e (tmul f m) :=
  congrArg e (nativeObjectIso_tmul M f m)

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFunctorExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)

theorem functorIso_ext
    (d e : (functor (k := k) (R := R) (S := S) (F := F)).obj M ≅ N)
    (h : ∀ (f : F) (m : M),
      d.hom.hom (letI := moduleCatBaseModule (k := k) (R := R) M; tmul f m) =
        e.hom.hom (letI := moduleCatBaseModule (k := k) (R := R) M; tmul f m)) : d = e := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  let := moduleCatBaseModule (k := k) (R := R) M
  let := moduleCatBaseTower (k := k) (R := R) M
  apply leftHom_ext
  exact h

end ArExplicit.BalancedTensor

end

end OAI
end


