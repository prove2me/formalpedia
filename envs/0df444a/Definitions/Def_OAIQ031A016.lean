-- Prove2me | Definitions.Def_OAIQ031A016
-- name    : OAIQ031A016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:00.49118+00:00
-- url     : https://prove2.me/theorems/ecc98931-f31d-4865-9aef-e52c6327e8e0
-- title:
--   Definitions bundle OAIQ031A016 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 12 definitions, 2 inductive types or structures, 17 instances and 17 theorems. The definitions and types are `OAI.ArExplicit.CoinducedModule`, `OAI.ArExplicit.CoinducedModule.coefficients`, `OAI.ArExplicit.CoinducedModule.coordinates`, `OAI.ArExplicit.CoinducedModule.embedding`, `OAI.ArExplicit.CoinducedModule.scalarEquiv`, `OAI.ArExplicit.ModuleBar.freeCoordinateScalar`, `OAI.ArExplicit.TwistedBimodule`, `OAI.ArExplicit.TwistedBimodule.coordinates`, `OAI.ArExplicit.TwistedBimodule.scalarLinearEquiv`, `OAI.ArExplicit.bimoduleEnvelopingModule`, `OAI.ArExplicit.bimoduleEnvelopingObject`, `OAI.ArExplicit.bimoduleEnvelopingRepresentation`, `OAI.ArExplicit.cokernelObject`, `OAI.ArExplicit.kernelObject`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarFreeCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarFreeCoordinate.lean), [`AuslanderReiten_Bar_NativeBarAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarAugmentation.lean), [`AuslanderReiten_Bar_NativeBarCompositeValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarCompositeValues.lean), [`AuslanderReiten_Bar_NativeBarFreeEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarFreeEndpoint.lean), [`AuslanderReiten_Homology_ChainComparisonIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ChainComparisonIso.lean), [`AuslanderReiten_Homology_RestrictKernelCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/RestrictKernelCokernel.lean), [`AuslanderReiten_Modules_BimoduleEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/BimoduleEnveloping.lean), [`AuslanderReiten_Modules_CoinducedModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/CoinducedModule.lean), [`AuslanderReiten_Modules_TwistedBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedBimodule.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A037`, `OAIQ031A038`, `OAIQ031A040` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarFreeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (e : M ≃ₗ[k] k)

def freeCoordinateScalar : (R ⊗[k] M) ≃ₗ[k] R :=
  (TensorProduct.congr (LinearEquiv.refl k R) e).trans (TensorProduct.rid k R)

omit [Module R M] [IsScalarTower k R M] in
@[simp] theorem freeCoordinateScalar_tmul (a : R) (m : M) :
    freeCoordinateScalar k R M e (a ⊗ₜ[k] m) = e m • a := by
  change (TensorProduct.rid k R) (a ⊗ₜ[k] e m) = _
  exact TensorProduct.rid_tmul _ _

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_RestrictKernelCokernel
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

def kernelObject : ModuleCat.{u} S := ModuleCat.of S (LinearMap.ker f.hom)
def cokernelObject : ModuleCat.{u} S := ModuleCat.of S (N ⧸ LinearMap.range f.hom)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ChainComparisonIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] {P Q R : ChainComplex C ℕ}

theorem comparisonIso_trans (e : P ≅ Q) (f : Q ≅ R) (m n : ℕ)
    (p : P.X m ⟶ P.X n) (q : Q.X m ⟶ Q.X n) (r : R.X m ⟶ R.X n)
    (he : p ≫ e.hom.f n = e.hom.f m ≫ q)
    (hf : q ≫ f.hom.f n = f.hom.f m ≫ r) :
    p ≫ (e ≪≫ f).hom.f n = (e ≪≫ f).hom.f m ≫ r := by
  change p ≫ (e.hom.f n ≫ f.hom.f n) = (e.hom.f m ≫ f.hom.f m) ≫ r
  rw [← Category.assoc, he, Category.assoc, hf, ← Category.assoc]

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
theorem compose_augmentation {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (d : D ⟶ E)
    (f : B ⟶ E) (u : A ⟶ F) (v : F ⟶ E)
    (hb : b ≫ d = f) (ha : a ≫ f = u ≫ v) :
    (a ≫ b) ≫ d = u ≫ v := by
  rw [Category.assoc, hb, ha]
universe u

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarFreeEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem valueOfEq {R : Type*} [Ring R] {X Y : ModuleCat R}
    {f g : X ⟶ Y} (h : f = g) {x : X} {y : Y} (hv : g x = y) : f x = y := by
  rw [h, hv]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarCompositeValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem valueOfMapEq {R : Type*} [Ring R] {X Y : ModuleCat R}
    {f g : X ⟶ Y} (h : f=g) {x : X} {y : Y} (hv : g x=y) : f x=y := by
  rw [h, hv]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedBimodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

@[ext] structure TwistedBimodule (k R : Type*) [CommRing k] [Ring R] [Algebra k R]
    (σ : R ≃ₐ[k] R) where
  value : R

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def coordinates : TwistedBimodule k R σ ≃ R where
  toFun := value
  invFun := TwistedBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (TwistedBimodule k R σ) := (coordinates σ).addCommGroup
instance instModule : Module R (TwistedBimodule k R σ) := (coordinates σ).addEquiv.module R
instance instModule_1 : Module k (TwistedBimodule k R σ) := (coordinates σ).addEquiv.module k

@[simp] theorem value_zero : (0 : TwistedBimodule k R σ).value = 0 := rfl
@[simp] theorem value_add (x y : TwistedBimodule k R σ) :
    (x + y).value = x.value + y.value := rfl
@[simp] theorem value_left_smul (r : R) (x : TwistedBimodule k R σ) :
    (r • x).value = r * x.value := rfl
@[simp] theorem value_scalar_smul (c : k) (x : TwistedBimodule k R σ) :
    (c • x).value = c • x.value := rfl

instance instSMulMulOpposite : SMul Rᵐᵒᵖ (TwistedBimodule k R σ) :=
  ⟨fun r x => ⟨x.value * σ r.unop⟩⟩

@[simp] theorem value_right_smul (r : Rᵐᵒᵖ) (x : TwistedBimodule k R σ) :
    (r • x).value = x.value * σ r.unop := rfl

instance instModuleMulOpposite : Module Rᵐᵒᵖ (TwistedBimodule k R σ) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [mul_assoc]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [add_mul]
  add_smul r s x := by ext; simp [mul_add]
  zero_smul x := by ext; simp

instance instSMulCommClassMulOpposite : SMulCommClass R Rᵐᵒᵖ (TwistedBimodule k R σ) where
  smul_comm r s x := by ext; exact (mul_assoc _ _ _).symm

instance instIsScalarTower : IsScalarTower k R (TwistedBimodule k R σ) where
  smul_assoc c r x := by ext; exact smul_mul_assoc c r x.value

instance instIsScalarTowerMulOpposite : IsScalarTower k Rᵐᵒᵖ (TwistedBimodule k R σ) where
  smul_assoc c r x := by
    ext
    change x.value * σ (c • r.unop) = c • (x.value * σ r.unop)
    rw [map_smul, mul_smul_comm]

def scalarLinearEquiv : TwistedBimodule k R σ ≃ₗ[k] R := (coordinates σ).addEquiv.linearEquiv k

instance instFinite_1 [Module.Finite k R] : Module.Finite k (TwistedBimodule k R σ) :=
  Module.Finite.equiv (scalarLinearEquiv σ).symm

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_BimoduleEnveloping
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

def bimoduleEnvelopingRepresentation : R ⊗[k] Rᵐᵒᵖ →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k M) (Algebra.lsmul k k M) (by
    intro a b
    apply LinearMap.ext
    intro x
    exact smul_comm a b x)

@[instance_reducible] def bimoduleEnvelopingModule : Module (R ⊗[k] Rᵐᵒᵖ) M :=
  Module.compHom M (bimoduleEnvelopingRepresentation k R M).toRingHom

def bimoduleEnvelopingObject : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) :=
  letI := bimoduleEnvelopingModule k R M
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M

instance instModuleCarrierTensorProductMulOppositeBimoduleEnvelopingObject : Module k (bimoduleEnvelopingObject k R M) := inferInstanceAs (Module k M)

omit [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M] in
@[simp] theorem bimoduleEnveloping_smul (a : R) (b : Rᵐᵒᵖ) (x : bimoduleEnvelopingObject k R M) :
    (a ⊗ₜ[k] b) • x = a • (b • (show M from x)) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_CoinducedModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

@[ext] structure CoinducedModule (k R M : Type*) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module k M] where
  functional : R →ₗ[k] M

namespace CoinducedModule

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M]

def coordinates : CoinducedModule k R M ≃ (R →ₗ[k] M) where
  toFun := functional
  invFun := CoinducedModule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (CoinducedModule k R M) := coordinates.addCommGroup
instance instModule : Module k (CoinducedModule k R M) := coordinates.addEquiv.module k

@[simp] theorem functional_zero (r : R) : (0 : CoinducedModule k R M).functional r = 0 := rfl
@[simp] theorem functional_add (f g : CoinducedModule k R M) (r : R) :
    (f + g).functional r = f.functional r + g.functional r := rfl
@[simp] theorem functional_smul (a : k) (f : CoinducedModule k R M) (r : R) :
    (a • f).functional r = a • f.functional r := rfl

instance instSMul : SMul R (CoinducedModule k R M) :=
  ⟨fun r f => ⟨{ toFun := fun t => f.functional (t * r)
                 map_add' := fun s t => by simp [add_mul]
                 map_smul' := fun a t => by simp }⟩⟩

@[simp] theorem functional_action (r t : R) (f : CoinducedModule k R M) :
    (r • f).functional t = f.functional (t * r) := rfl

instance instModule_1 : Module R (CoinducedModule k R M) where
  one_smul f := by ext t; simp
  mul_smul r s f := by ext t; simp [mul_assoc]
  smul_zero r := by ext t; simp
  smul_add r f g := by ext t; simp
  zero_smul f := by ext t; simp
  add_smul r s f := by ext t; simp [mul_add]

instance instIsScalarTower : IsScalarTower k R (CoinducedModule k R M) where
  smul_assoc a r f := by ext t; simp

instance instSMulCommClass : SMulCommClass k R (CoinducedModule k R M) where
  smul_comm a r f := by ext t; rfl

def scalarEquiv : CoinducedModule k R M ≃ₗ[k] (R →ₗ[k] M) :=
  coordinates.addEquiv.linearEquiv k

instance instFinite [Module.Finite k R] [Module.Finite k M] : Module.Finite k (CoinducedModule k R M) :=
  Module.Finite.equiv scalarEquiv.symm

section Embedding

variable [Module R M] [IsScalarTower k R M]

def embedding : M →ₗ[R] CoinducedModule k R M where
  toFun m := ⟨{ toFun := fun t => t • m
                map_add' := fun r s => add_smul r s m
                map_smul' := fun a r => smul_assoc a r m }⟩
  map_add' m n := by ext t; exact smul_add t m n
  map_smul' r m := by ext t; exact (mul_smul t r m).symm

@[simp] theorem embedding_apply (m : M) (t : R) :
    (embedding (k := k) m).functional t = t • m := rfl

theorem embedding_injective : Function.Injective (embedding (k := k) (R := R) (M := M)) := by
  intro m n h
  have h' := congrArg (fun f : CoinducedModule k R M => f.functional 1) h
  simpa using h'

end Embedding

variable [Module.Finite k M]

def coefficients : M ≃ₗ[k] (Fin (Module.finrank k M) → k) :=
  (Module.finBasis k M).equivFun

end CoinducedModule
end ArExplicit

end

end OAI
end


