-- Prove2me | Definitions.Def_OAIQ031A025
-- name    : OAIQ031A025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:03:41.98999+00:00
-- url     : https://prove2.me/theorems/d7beec13-2ea2-4e37-8ee6-af5f2bfa5ba1
-- title:
--   Definitions bundle OAIQ031A025 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 14 definitions, 2 instances and 19 theorems. The definitions and types are `OAI.ArExplicit.A.Simple`, `OAI.ArExplicit.A.augmentation`, `OAI.ArExplicit.A.augmentationIdeal`, `OAI.ArExplicit.A.simpleCharacter`, `OAI.ArExplicit.A.simpleCoordinate`, `OAI.ArExplicit.A.simpleGenerator`, `OAI.ArExplicit.A.socleMap`, `OAI.ArExplicit.ExternalTensor.regularEquiv`, `OAI.ArExplicit.Resolution.uPreimage`, `OAI.ArExplicit.T.coordinateEquiv`, `OAI.ArExplicit.T.simpleActionAt`, `OAI.ArExplicit.T.simpleCharacter`, `OAI.ArExplicit.T.socleMap`, `OAI.ArExplicit.T.tensorRightCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_BaseAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseAlgebra.lean), [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Algebras_TCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TCoordinates.lean), [`AuslanderReiten_Algebras_TSimple`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TSimple.lean), [`AuslanderReiten_Algebras_TSocle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TSocle.lean), [`AuslanderReiten_Algebras_TensorSimple`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorSimple.lean), [`AuslanderReiten_Bar_TCasimir`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimir.lean), [`AuslanderReiten_Bar_TCasimirAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimirAugmentation.lean), [`AuslanderReiten_Bar_TCasimirEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimirEvaluation.lean), [`AuslanderReiten_Evaluation_TensorBeta`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorBeta.lean), [`AuslanderReiten_Tensor_ExternalTensorModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorModule.lean), [`AuslanderReiten_Tensor_ExternalTensorRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorRegular.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001` and `OAIQ031A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A044`, `OAIQ031A046`, `OAIQ031A047`, `OAIQ031A051` and `OAIQ031A052`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseAlgebra
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace BaseAlgebra

variable {k : Type*} (q : k)

variable [CommRing k]

open Letter

instance instFinite : Module.Finite k (BaseAlgebra k q) :=
  Module.Finite.equiv (coordinateLinearEquiv q).symm

end BaseAlgebra
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleModule
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem F_expand (a : F q) : (a : C) =
    (a : C).coeff f • basisVector q f + (a : C).coeff u • basisVector q u +
    (a : C).coeff v • basisVector q v + (a : C).coeff n • basisVector q n := by
  ext i
  cases i <;> simp

def uPreimage (α β γ : k) : E q :=
  ⟨α • basisVector q e + β • basisVector q x + (γ / (1 + q)) • basisVector q t, by
    change (_ : C) * basisVector q e = _
    simp [add_mul, basis_mul, multiplicationTable]⟩

theorem uPreimage_spec (α β γ : k) (hq : 1 + q ≠ 0) :
    (uPreimage q α β γ : C) * basisVector q u =
      α • basisVector q u + β • basisVector q v + γ • basisVector q n := by
  rw [mul_u_formula]
  have hγ : (1 + q) * (γ / (1 + q)) = γ := by rw [mul_comm, div_mul_cancel₀ γ hq]
  simp [uPreimage, hγ]

theorem mem_range_dU_iff (hq : 1 + q ≠ 0) (a : F q) :
    a ∈ LinearMap.range (dU q) ↔ (a : C).coeff f = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp [product]
  · intro ha
    refine ⟨uPreimage q ((a : C).coeff u) ((a : C).coeff v) ((a : C).coeff n), ?_⟩
    apply Subtype.ext
    rw [coe_dU, uPreimage_spec q _ _ _ hq]
    simpa [ha] using (F_expand q a).symm

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace T

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

theorem base_expand (a : BaseAlgebra k q) :
    a = ∑ i : Letter, a.coeff i • basisVector q i := by
  apply BaseAlgebra.ext
  funext aidx
  change a.coeff aidx = BaseAlgebra.coordinateLinearEquiv q (∑ i : Letter, a.coeff i • basisVector q i) aidx
  rw [map_sum]
  have hb : ∀ i : Letter, BaseAlgebra.coordinateLinearEquiv q (basisVector q i) = Pi.single i 1 := by
    intro i
    rfl
  simp [hb, Pi.single_apply]

theorem coordinate_ext {a b : T k q} (h : ∀ i, coefficient q i a = coefficient q i b) : a = b := by
  apply TrivialExtension.ext
  · apply BaseAlgebra.ext
    funext i
    exact h (false, i)
  · apply LinearMap.ext
    intro c
    rw [base_expand q c]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x => c.coeff i • x) (h (true, i))

theorem expand (a : T k q) : a = ∑ i : TIndex, coefficient q i a • vector q i := by
  apply coordinate_ext q
  intro bidx
  simp

def coordinateEquiv : T k q ≃ₗ[k] (TIndex → k) where
  toFun a i := coefficient q i a
  invFun c := ∑ i, c i • vector q i
  left_inv a := (expand q a).symm
  right_inv c := by funext i; simp
  map_add' a b := by funext i; simp
  map_smul' r a := by funext i; simp

end T
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TSimple
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace T

variable {k : Type*} [Field k] (q : k)

def simpleCharacter : T k q →ₐ[k] k where
  toFun a := a.base.coeff .f
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one]

end T

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TSocle
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem mul_upper_f (a : T k q) : a * upper q .f = simpleCharacter q a • upper q .f := by
  apply TrivialExtension.ext
  · simp [upper, TrivialExtension.inr]
  · apply LinearMap.ext
    intro c
    change (c * a.base).coeff .f + a.dual (0 * c) = a.base.coeff .f * c.coeff .f
    simp [BaseAlgebra.coeff_mul, BaseAlgebra.product, mul_comm]

def socleMap : Resolution.Simple q →ₗ[T k q] T k q where
  toFun s := Resolution.simpleCoordinate q s • upper q .f
  map_add' x y := by simp [add_smul]
  map_smul' a s := by
    change Resolution.simpleCoordinate q (a • s) • upper q .f =
      a * (Resolution.simpleCoordinate q s • upper q .f)
    rw [Resolution.t_simple_character, mul_smul_comm, mul_upper_f]
    change (a.base.coeff .f * Resolution.simpleCoordinate q s) • upper q .f =
      Resolution.simpleCoordinate q s • (a.base.coeff .f • upper q .f)
    rw [smul_smul, mul_comm]

@[simp] theorem socleMap_generator : socleMap q (CocycleData.simpleGenerator q) = upper q .f := by
  simp [socleMap]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorModule
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module k M] [Module k N] [Module A M] [Module B N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

instance baseModule : Module k (moduleObject k A B M N) :=
  inferInstanceAs (Module k (M ⊗[k] N))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorRegular
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def regularEquiv : moduleObject k A B A B ≃ₗ[A ⊗[k] B] (A ⊗[k] B) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    let w : A ⊗[k] B := z
    change representation k A B A B a w = a * w
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
    | tmul a b =>
      induction w using OAI.tensorInductionOn with
      | add x y hx hy => simp only [map_add, mul_add, hx, hy]
      | tmul x y =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl

@[simp] theorem regularEquiv_apply (x : moduleObject k A B A B) :
    regularEquiv k A B x = (x : A ⊗[k] B) := rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorSimple
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

abbrev Simple := ExternalTensor.moduleObject k R R S S

def simpleCoordinate : S ⊗[k] S →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (Resolution.simpleCoordinate q) (Resolution.simpleCoordinate q))

@[simp] theorem simpleCoordinate_tmul (s t : S) :
    simpleCoordinate q (s ⊗ₜ[k] t) =
      Resolution.simpleCoordinate q s * Resolution.simpleCoordinate q t := rfl

def simpleGenerator : Simple q := CocycleData.simpleGenerator q ⊗ₜ[k] CocycleData.simpleGenerator q

@[simp] theorem simpleGenerator_coordinate : simpleCoordinate q (simpleGenerator q) = 1 := by
  simp [simpleGenerator]

def simpleCharacter : A k q →ₐ[k] k :=
  Algebra.TensorProduct.lift (T.simpleCharacter q) (T.simpleCharacter q)
    (fun _ _ => Commute.all _ _)

@[simp] theorem simpleCharacter_tmul (a b : R) :
    simpleCharacter q (a ⊗ₜ[k] b) = T.simpleCharacter q a * T.simpleCharacter q b := rfl

def augmentationIdeal : Ideal (A k q) := RingHom.ker (simpleCharacter q)

def socleMap : Simple q →ₗ[A k q] A k q :=
  (ExternalTensor.regularEquiv k R R).toLinearMap.comp
    (ExternalTensor.map k R R (T.socleMap q) (T.socleMap q))

@[simp] theorem socleMap_tmul (s t : S) :
    socleMap q (s ⊗ₜ[k] t) = T.socleMap q s ⊗ₜ[k] T.socleMap q t := rfl

@[simp] theorem socleMap_generator :
    socleMap q (simpleGenerator q) = T.upper q .f ⊗ₜ[k] T.upper q .f := by
  simp [simpleGenerator]

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimir
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

@[simp] theorem star_star (i : TIndex) : i.star.star = i := by
  obtain ⟨b, i⟩ := i
  cases b <;> rfl

def tensorRightCoordinates : R ⊗[k] R ≃ₗ[k] (TIndex → R) :=
  (TensorProduct.congr (LinearEquiv.refl k R) (coordinateEquiv q)).trans
    (TensorProduct.piScalarRight k k R TIndex)

@[simp] theorem tensorRightCoordinates_tmul (a b : R) (i : TIndex) :
    tensorRightCoordinates q (a ⊗ₜ[k] b) i = coefficient q i b • a := by
  simp [tensorRightCoordinates, coordinateEquiv]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirAugmentation
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

@[simp] theorem coordinateFunctional_apply (i : Letter) (a : BaseAlgebra k q) :
    coordinateFunctional q i a = a.coeff i := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirEvaluation
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def simpleActionAt (s : S) : R →ₗ[k] S :=
  ((Algebra.lsmul k k S).toLinearMap).flip s

@[simp] theorem simpleActionAt_apply (s : S) (a : R) : simpleActionAt q s a = a • s := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorBeta
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

@[simp] theorem simpleCoordinate_zero : simpleCoordinate q (0 : Simple q) = 0 := by
  change simpleCoordinate q (0 : Resolution.Simple q ⊗[k] Resolution.Simple q) = 0
  exact map_zero _

def augmentation : A k q →ₗ[A k q] Simple q where
  toFun a := a • simpleGenerator q
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

end ArExplicit.A

end

end OAI
end


