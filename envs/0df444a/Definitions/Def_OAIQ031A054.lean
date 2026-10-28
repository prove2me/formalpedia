-- Prove2me | Definitions.Def_OAIQ031A054
-- name    : OAIQ031A054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:06:17.626061+00:00
-- url     : https://prove2.me/theorems/58770cf2-bade-4b00-bbcd-0a8adc8f153c
-- title:
--   Definitions bundle OAIQ031A054 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 7 definitions, 1 instance and 11 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.doubleLift`, `OAI.ArExplicit.EnvelopingBimodule.evaluationFunctor`, `OAI.ArExplicit.ExternalBalanced.forward`, `OAI.ArExplicit.ExternalBalanced.forwardPair`, `OAI.ArExplicit.ExternalBalanced.inverse`, `OAI.ArExplicit.ExternalBalanced.rawForward`, `OAI.ArExplicit.ExternalBalanced.rawInverse`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Tensor_BalancedTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorAction.lean), [`AuslanderReiten_Tensor_BalancedTensorDoubleLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorDoubleLift.lean), [`AuslanderReiten_Tensor_EnvelopingEvaluationFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingEvaluationFunctor.lean), [`AuslanderReiten_Tensor_ExternalBalancedCore`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedCore.lean), [`AuslanderReiten_Tensor_ExternalBalancedEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedEquiv.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A015` and `OAIQ031A026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A070`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A015
import Definitions.Def_OAIQ031A026

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorAction
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

open TensorProduct

variable {k R F M S : Type*} [CommRing k] [Ring R] [Ring S]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

variable [Algebra k S] [IsScalarTower k S F]

instance instSMulCommClass : SMulCommClass k S (BalancedTensor k R F M) where
  smul_comm c s z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
        change Submodule.Quotient.mk (c • s • z) =
          (Submodule.Quotient.mk (s • c • z) : BalancedTensor k R F M)
        rw [smul_comm]

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorDoubleLift
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open scoped TensorProduct
universe u
variable {k A B F G X Y Z : Type u} [CommRing k] [Ring A] [Ring B]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module k F] [Module k G] [Module k X] [Module k Y] [Module k Z]
  [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y]

def doubleLift (b : F →ₗ[k] X →ₗ[k] G →ₗ[k] Y →ₗ[k] Z)
    (hA : ∀ (f : F) (a : A) (x : X) (g : G) (y : Y), b (MulOpposite.op a • f) x g y = b f (a • x) g y)
    (hB : ∀ (f : F) (x : X) (g : G) (a : B) (y : Y), b f x (MulOpposite.op a • g) y = b f x g (a • y)) :
    BalancedTensor k A F X →ₗ[k] BalancedTensor k B G Y →ₗ[k] Z :=
  lift
    { toFun f :=
        { toFun x := lift (b f x) (hB f x)
          map_add' x x' := by
            apply hom_ext
            intro g y
            simp only [lift_tmul, map_add, LinearMap.add_apply]
          map_smul' a x := by
            apply hom_ext
            intro g y
            simp only [lift_tmul, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
      map_add' f f' := by
        apply LinearMap.ext
        intro x
        apply hom_ext
        intro g y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, lift_tmul, map_add, LinearMap.add_apply]
      map_smul' a f := by
        apply LinearMap.ext
        intro x
        apply hom_ext
        intro g y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, lift_tmul, map_smul,
          LinearMap.smul_apply, RingHom.id_apply] }
    (by
      intro f a x
      apply hom_ext
      intro g y
      exact hA f a x g y)

@[simp] theorem doubleLift_tmul (b : F →ₗ[k] X →ₗ[k] G →ₗ[k] Y →ₗ[k] Z)
    (hA : ∀ (f : F) (a : A) (x : X) (g : G) (y : Y), b (MulOpposite.op a • f) x g y = b f (a • x) g y)
    (hB : ∀ (f : F) (x : X) (g : G) (a : B) (y : Y), b f x (MulOpposite.op a • g) y = b f x g (a • y))
    (f : F) (x : X) (g : G) (y : Y) :
    doubleLift b hA hB (tmul f x) (tmul g y) = b f x g y := rfl

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingEvaluationFunctor
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

def evaluationFunctor : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (BalancedTensor k R (EnvelopingBimodule k R M) X)
  map f := ModuleCat.ofHom (tensorMap X f)
  map_id M := by apply ModuleCat.hom_ext; exact tensorMap_id X
  map_comp f g := by apply ModuleCat.hom_ext; exact tensorMap_comp X f g

omit [IsScalarTower k R X] in
@[simp] theorem evaluationFunctor_map_tmul
    {M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)} (f : M ⟶ N)
    (m : EnvelopingBimodule k R M) (x : X) :
    (evaluationFunctor k R X).map f (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (map f m) x := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedCore
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open scoped TensorProduct
universe u
variable {k A B E V F G X Y : Type u} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  [AddCommGroup E] [AddCommGroup V] [AddCommGroup F] [AddCommGroup G]
  [AddCommGroup X] [AddCommGroup Y]
  [Module k E] [Module k V] [Module k F] [Module k G] [Module k X] [Module k Y]
  [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V]
  [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y]

variable (e : E ≃ₗ[k] F ⊗[k] G) (v : V ≃ₗ[k] X ⊗[k] Y)
local notation "Sbal" => BalancedTensor k (A ⊗[k] B) E V
local notation "Lbal" => BalancedTensor k A F X
local notation "Rbal" => BalancedTensor k B G Y

def rawForward : (E ⊗[k] V) →ₗ[k] Lbal ⊗[k] Rbal :=
  (TensorProduct.map (balancingRelations k A F X).mkQ
    (balancingRelations k B G Y).mkQ).comp
    ((TensorProduct.tensorTensorTensorComm k F G X Y).toLinearMap.comp
      (TensorProduct.map e.toLinearMap v.toLinearMap))

def forwardPair : E →ₗ[k] V →ₗ[k] Lbal ⊗[k] Rbal := TensorProduct.curry (rawForward (A := A) (B := B) e v)

omit [Algebra k A] [Algebra k B] [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V] in
@[simp] theorem forwardPair_pure (f : F) (g : G) (x : X) (y : Y) :
    forwardPair (A := A) (B := B) e v (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y)) =
      BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y := by
  simp [forwardPair, rawForward, BalancedTensor.tmul]

variable
  (he : ∀ (a : A) (b : B) (f : F) (g : G),
    MulOpposite.op (a ⊗ₜ[k] b) • e.symm (f ⊗ₜ[k] g) =
      e.symm ((MulOpposite.op a • f) ⊗ₜ[k] (MulOpposite.op b • g)))
  (hv : ∀ (a : A) (b : B) (x : X) (y : Y),
    (a ⊗ₜ[k] b) • v.symm (x ⊗ₜ[k] y) = v.symm ((a • x) ⊗ₜ[k] (b • y)))

include he hv

 theorem forwardPair_balanced (z : E) (r : A ⊗[k] B) (w : V) :
    forwardPair (A := A) (B := B) e v (MulOpposite.op r • z) w = forwardPair (A := A) (B := B) e v z (r • w) := by
  obtain ⟨z, rfl⟩ := e.symm.surjective z
  obtain ⟨w, rfl⟩ := v.symm.surjective w
  induction r using OAI.tensorInductionOn with
  | add r s hr hs => simp only [MulOpposite.op_add, add_smul, map_add, LinearMap.add_apply, hr, hs]
  | tmul a b =>
    induction z using OAI.tensorInductionOn with
    | add z z' hz hz' => simp only [map_add, smul_add, LinearMap.add_apply, hz, hz']
    | tmul f g =>
      induction w using OAI.tensorInductionOn with
      | add w w' hw hw' => simp only [map_add, smul_add, hw, hw']
      | tmul x y => rw [he, hv, forwardPair_pure, forwardPair_pure,
          BalancedTensor.balance, BalancedTensor.balance]

def forward : Sbal →ₗ[k] Lbal ⊗[k] Rbal :=
  BalancedTensor.lift (forwardPair (A := A) (B := B) e v) (forwardPair_balanced (A := A) (B := B) e v he hv)

@[simp] theorem forward_pure (f : F) (g : G) (x : X) (y : Y) :
    forward (A := A) (B := B) e v he hv (BalancedTensor.tmul (R := A ⊗[k] B) (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y))) =
      BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y :=
  forwardPair_pure (A := A) (B := B) e v f g x y

def rawInverse : ((F ⊗[k] X) ⊗[k] (G ⊗[k] Y)) →ₗ[k] Sbal :=
  (TensorProduct.lift (BalancedTensor.mk (k := k) (R := A ⊗[k] B))).comp
    ((TensorProduct.map e.symm.toLinearMap v.symm.toLinearMap).comp
      (TensorProduct.tensorTensorTensorComm k F X G Y).toLinearMap)

omit he hv [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y] in
@[simp] theorem rawInverse_pure (f : F) (x : X) (g : G) (y : Y) :
    rawInverse (A := A) (B := B) e v ((f ⊗ₜ[k] x) ⊗ₜ[k] (g ⊗ₜ[k] y)) =
      BalancedTensor.tmul (R := A ⊗[k] B) (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y)) := rfl

 theorem inverse_balanced_left (f : F) (a : A) (x : X) (g : G) (y : Y) :
    BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) (MulOpposite.op a • f) x g y =
      BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) f (a • x) g y := by
  simpa only [BalancedTensor.curryFour_apply, rawInverse_pure, he, hv,
    MulOpposite.op_one, one_smul] using
    (BalancedTensor.balance (k := k) (R := A ⊗[k] B)
      (e.symm (f ⊗ₜ[k] g)) (a ⊗ₜ[k] (1 : B)) (v.symm (x ⊗ₜ[k] y)))

 theorem inverse_balanced_right (f : F) (x : X) (g : G) (b : B) (y : Y) :
    BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) f x (MulOpposite.op b • g) y =
      BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v) f x g (b • y) := by
  simpa only [BalancedTensor.curryFour_apply, rawInverse_pure, he, hv,
    MulOpposite.op_one, one_smul] using
    (BalancedTensor.balance (k := k) (R := A ⊗[k] B)
      (e.symm (f ⊗ₜ[k] g)) ((1 : A) ⊗ₜ[k] b) (v.symm (x ⊗ₜ[k] y)))

def inverse : (Lbal ⊗[k] Rbal) →ₗ[k] Sbal :=
  TensorProduct.lift (BalancedTensor.doubleLift (BalancedTensor.curryFour (rawInverse (A := A) (B := B) e v))
    (inverse_balanced_left (A := A) (B := B) e v he hv) (inverse_balanced_right (A := A) (B := B) e v he hv))

@[simp] theorem inverse_pure (f : F) (x : X) (g : G) (y : Y) :
    inverse (A := A) (B := B) e v he hv (BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y) =
      BalancedTensor.tmul (R := A ⊗[k] B) (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y)) := rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedEquiv
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open scoped TensorProduct
universe u
variable {k A B E V F G X Y : Type u} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  [AddCommGroup E] [AddCommGroup V] [AddCommGroup F] [AddCommGroup G]
  [AddCommGroup X] [AddCommGroup Y]
  [Module k E] [Module k V] [Module k F] [Module k G] [Module k X] [Module k Y]
  [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V]
  [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y]

variable (e : E ≃ₗ[k] F ⊗[k] G) (v : V ≃ₗ[k] X ⊗[k] Y)
local notation "Sbal" => BalancedTensor k (A ⊗[k] B) E V
local notation "Lbal" => BalancedTensor k A F X
local notation "Rbal" => BalancedTensor k B G Y

variable
  (he : ∀ (a : A) (b : B) (f : F) (g : G),
    MulOpposite.op (a ⊗ₜ[k] b) • e.symm (f ⊗ₜ[k] g) =
      e.symm ((MulOpposite.op a • f) ⊗ₜ[k] (MulOpposite.op b • g)))
  (hv : ∀ (a : A) (b : B) (x : X) (y : Y),
    (a ⊗ₜ[k] b) • v.symm (x ⊗ₜ[k] y) = v.symm ((a • x) ⊗ₜ[k] (b • y)))

include he hv

theorem inverse_forward (z : Sbal) :
    inverse (A := A) (B := B) e v he hv (forward e v he hv z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    obtain ⟨z, rfl⟩ := e.symm.surjective z
    obtain ⟨w, rfl⟩ := v.symm.surjective w
    induction z using OAI.tensorInductionOn with
    | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, hz, hz']
    | tmul f g =>
      induction w using OAI.tensorInductionOn with
      | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, hw, hw']
      | tmul x y => rw [forward_pure, inverse_pure]

theorem forward_inverse (z : Lbal ⊗[k] Rbal) :
    forward (A := A) (B := B) e v he hv (inverse e v he hv z) = z := by
  induction z using OAI.tensorInductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [TensorProduct.add_tmul, map_add, hz, hz']
    | tmul f x =>
      induction w using BalancedTensor.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
      | tmul g y => rw [inverse_pure, forward_pure]

end ArExplicit.ExternalBalanced

end

end OAI
end


