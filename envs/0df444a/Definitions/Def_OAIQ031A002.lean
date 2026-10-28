-- Prove2me | Definitions.Def_OAIQ031A002
-- name    : OAIQ031A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:59:05.629608+00:00
-- url     : https://prove2.me/theorems/d010f5ec-2bb7-4322-9d60-191b0be907e0
-- title:
--   Definitions bundle OAIQ031A002 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 25 definitions, 2 inductive types or structures, 11 instances and 29 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.Cochain3`, `OAI.ArExplicit.BalancedTensor`, `OAI.ArExplicit.BalancedTensor.lift`, `OAI.ArExplicit.BalancedTensor.mk`, `OAI.ArExplicit.BalancedTensor.tmul`, `OAI.ArExplicit.EnvelopingBimodule`, `OAI.ArExplicit.EnvelopingBimodule.coordinates`, `OAI.ArExplicit.EnvelopingBimodule.map`, `OAI.ArExplicit.EnvelopingBimodule.piInclusion`, `OAI.ArExplicit.EnvelopingBimodule.piObject`, `OAI.ArExplicit.EnvelopingBimodule.piProjection`, `OAI.ArExplicit.EnvelopingBimodule.regularObject`, `OAI.ArExplicit.EnvelopingBimodule.regularRaw`, `OAI.ArExplicit.EnvelopingBimodule.scalarEquiv`, `OAI.ArExplicit.EnvelopingBimodule.unopAction`, `OAI.ArExplicit.FactorsThroughFiniteFree`, `OAI.ArExplicit.FactorsThroughFiniteProjective`, `OAI.ArExplicit.FiniteLeftModule`, `OAI.ArExplicit.FiniteLeftModule.canonicalFreeCover`, `OAI.ArExplicit.FiniteLeftModule.freeCoverMapScalar`, `OAI.ArExplicit.StableHom`, `OAI.ArExplicit.StableHom.classOf`, `OAI.ArExplicit.TrivialExtension.twist`, `OAI.ArExplicit.balancingRelations`, `OAI.ArExplicit.projectiveMaps`, `OAI.ArExplicit.tensorLeftInclusion`, `OAI.ArExplicit.tensorRightInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCochain.lean), [`AuslanderReiten_Complete_FiniteCompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FiniteCompleteResolution.lean), [`AuslanderReiten_Coordinates_TensorRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorRestriction.lean), [`AuslanderReiten_Fibers_FiniteModuleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteModuleFiber.lean), [`AuslanderReiten_Modules_Twist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/Twist.lean), [`AuslanderReiten_Stable_StableHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHom.lean), [`AuslanderReiten_Tensor_BalancedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensor.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedMap.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedProjective.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedRegular.lean), [`AuslanderReiten_Tensor_EnvelopingBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBimodule.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A025`, `OAIQ031A026`, `OAIQ031A027`, `OAIQ031A030`, `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A037`, `OAIQ031A038`, `OAIQ031A039` and `OAIQ031A040`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev Cochain3 := R →ₗ[k] R →ₗ[k] R →ₗ[k] R

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_FiniteCompleteResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

structure FiniteLeftModule where
  carrier : ModuleCat.{u} R
  [scalar : Module k carrier]
  [tower : IsScalarTower k R carrier]
  [finite : Module.Finite k carrier]

attribute [instance] FiniteLeftModule.scalar FiniteLeftModule.tower FiniteLeftModule.finite

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorRestriction
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

def tensorLeftInclusion : R →+* R ⊗[k] S :=
  (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S).toRingHom

def tensorRightInclusion : S →+* R ⊗[k] S :=
  (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S).toRingHom

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteModuleFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory
open scoped TensorProduct

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

def canonicalFreeCover (Y : FiniteLeftModule k R) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (R ⊗[k] Y.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstanceAs (Module.Finite k (R ⊗[k] Y.carrier))

def freeCoverMapScalar (Y : FiniteLeftModule k R) : R ⊗[k] Y.carrier →ₗ[k] Y.carrier :=
  TensorProduct.lift
    { toFun := fun r =>
        { toFun := fun y => r • y
          map_add' := smul_add r
          map_smul' := fun a y => by
            rw [← IsScalarTower.algebraMap_smul R a y, ← mul_smul,
              ← Algebra.commutes, mul_smul, IsScalarTower.algebraMap_smul]
            rfl }
      map_add' := fun r s => by ext y; exact add_smul r s y
      map_smul' := fun a r => by ext y; exact smul_assoc a r y }

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_Twist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def twist (h : kˣ) : TrivialExtension k A ≃ₐ[k] TrivialExtension k A where
  toFun a := ⟨a.base, (h : k) • a.dual⟩
  invFun a := ⟨a.base, (↑h⁻¹ : k) • a.dual⟩
  left_inv a := by
    apply TrivialExtension.ext
    · rfl
    · simp [smul_smul]
  right_inv a := by
    apply TrivialExtension.ext
    · rfl
    · simp [smul_smul]
  map_add' a b := by
    apply TrivialExtension.ext
    · rfl
    · exact smul_add _ _ _
  map_mul' a b := by
    apply TrivialExtension.ext
    · rfl
    · ext c
      change (h : k) * (b.dual (c * a.base) + a.dual (b.base * c)) =
        (h : k) * b.dual (c * a.base) + (h : k) * a.dual (b.base * c)
      exact mul_add _ _ _
  commutes' c := by
    apply TrivialExtension.ext
    · rfl
    · change (h : k) • (algebraMap k (TrivialExtension k A) c).dual =
        (algebraMap k (TrivialExtension k A) c).dual
      simp only [Algebra.algebraMap_eq_smul_one, dual_smul, dual_one, smul_zero]

@[simp] theorem twist_base (h : kˣ) (a : TrivialExtension k A) :
    (twist h a).base = a.base := rfl

@[simp] theorem twist_dual (h : kˣ) (a : TrivialExtension k A) :
    (twist h a).dual = (h : k) • a.dual := rfl

@[simp] theorem twist_inl (h : kˣ) (a : A) : twist h (inl a) = inl a := by
  apply TrivialExtension.ext
  · rfl
  · exact smul_zero _

@[simp] theorem twist_inr (h : kˣ) (φ : Module.Dual k A) :
    twist h (inr φ) = inr ((h : k) • φ) := rfl

end ArExplicit.TrivialExtension

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace ArExplicit

variable (R : Type u) [Ring R]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

def FactorsThroughFiniteFree (f : M →ₗ[R] N) : Prop :=
  ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
    (_ : Module.Free R P) (_ : Module.Finite R P)
    (i : M →ₗ[R] P) (p : P →ₗ[R] N), p.comp i = f

def FactorsThroughFiniteProjective (f : M →ₗ[R] N) : Prop :=
  ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
    (_ : Module.Projective R P) (_ : Module.Finite R P)
    (i : M →ₗ[R] P) (p : P →ₗ[R] N), p.comp i = f

variable {R M N}

theorem factorsThroughFiniteFree_zero :
    FactorsThroughFiniteFree R M N (0 : M →ₗ[R] N) := by
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, 0, 0, rfl⟩

theorem FactorsThroughFiniteFree.add {f g : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) (hg : FactorsThroughFiniteFree R M N g) :
    FactorsThroughFiniteFree R M N (f + g) := by
  rcases hf with ⟨P, hP, hRP, hfreeP, hfiniteP, i, p, rfl⟩
  rcases hg with ⟨Q, hQ, hRQ, hfreeQ, hfiniteQ, j, q, rfl⟩
  refine ⟨P × Q, inferInstance, inferInstance, inferInstance, inferInstance,
    i.prod j, p.coprod q, ?_⟩
  ext x
  rfl

theorem FactorsThroughFiniteFree.neg {f : M →ₗ[R] N}
    (hf : FactorsThroughFiniteFree R M N f) :
    FactorsThroughFiniteFree R M N (-f) := by
  rcases hf with ⟨P, hP, hRP, hfreeP, hfiniteP, i, p, rfl⟩
  refine ⟨P, hP, hRP, hfreeP, hfiniteP, i, -p, ?_⟩
  ext x
  rfl

variable {L P : Type u} [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]

variable (R M N)

def projectiveMaps : AddSubgroup (M →ₗ[R] N) where
  carrier := FactorsThroughFiniteFree R M N
  zero_mem' := factorsThroughFiniteFree_zero
  add_mem' := FactorsThroughFiniteFree.add
  neg_mem' := FactorsThroughFiniteFree.neg

abbrev StableHom := (M →ₗ[R] N) ⧸ projectiveMaps R M N

namespace StableHom

def classOf : (M →ₗ[R] N) →+ StableHom R M N :=
  QuotientAddGroup.mk' (projectiveMaps R M N)

end StableHom

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable (k R F M : Type*) [CommRing k] [Ring R]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]

def balancingRelations : Submodule k (F ⊗[k] M) :=
  Submodule.span k {z | ∃ (f : F) (r : R) (m : M),
    z = (MulOpposite.op r • f) ⊗ₜ[k] m - f ⊗ₜ[k] (r • m)}

abbrev BalancedTensor := (F ⊗[k] M) ⧸ balancingRelations k R F M

namespace BalancedTensor

variable {k R F M}

def tmul (f : F) (m : M) : BalancedTensor k R F M :=
  (balancingRelations k R F M).mkQ (f ⊗ₜ[k] m)

@[simp] theorem zero_tmul (m : M) : tmul (k := k) (R := R) (0 : F) m = 0 := by
  simp [tmul]

@[simp] theorem tmul_zero (f : F) : tmul (k := k) (R := R) f (0 : M) = 0 := by
  simp [tmul]

theorem add_tmul (f g : F) (m : M) :
    tmul (k := k) (R := R) (f + g) m = tmul f m + tmul g m := by simp [tmul, TensorProduct.add_tmul]

theorem tmul_add (f : F) (m n : M) :
    tmul (k := k) (R := R) f (m + n) = tmul f m + tmul f n := by simp [tmul, TensorProduct.tmul_add]

theorem scalar_tmul (c : k) (f : F) (m : M) :
    tmul (k := k) (R := R) (c • f) m = c • tmul f m := by
  exact (balancingRelations k R F M).mkQ.map_smul c (f ⊗ₜ[k] m)

theorem tmul_scalar (c : k) (f : F) (m : M) :
    tmul (k := k) (R := R) f (c • m) = c • tmul f m := by simp [tmul]

theorem balance (f : F) (r : R) (m : M) :
    tmul (k := k) (R := R) (MulOpposite.op r • f) m = tmul f (r • m) := by
  apply (Submodule.Quotient.eq (balancingRelations k R F M)).mpr
  exact Submodule.subset_span ⟨f, r, m, rfl⟩

def mk : F →ₗ[k] M →ₗ[k] BalancedTensor k R F M where
  toFun f :=
    { toFun := tmul f
      map_add' := tmul_add f
      map_smul' := fun c m => tmul_scalar c f m }
  map_add' f g := by ext m; exact add_tmul f g m
  map_smul' c f := by ext m; exact scalar_tmul c f m

variable {N : Type*} [AddCommGroup N] [Module k N]

def lift (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m)) :
    BalancedTensor k R F M →ₗ[k] N :=
  (balancingRelations k R F M).liftQ (TensorProduct.lift b) (by
    apply Submodule.span_le.mpr
    rintro z ⟨f, r, m, rfl⟩
    change TensorProduct.lift b ((MulOpposite.op r • f) ⊗ₜ[k] m - f ⊗ₜ[k] (r • m)) = 0
    simp only [map_sub, TensorProduct.lift.tmul, hb, sub_self])

@[simp] theorem lift_tmul (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m)) (f : F) (m : M) :
    lift b hb (tmul f m) = b f m := rfl

end BalancedTensor
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBimodule
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

@[ext] structure EnvelopingBimodule (k R : Type u) [Field k] [Ring R] [Algebra k R]
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) where
  value : M

namespace EnvelopingBimodule

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

def coordinates : EnvelopingBimodule k R M ≃ M where
  toFun := value
  invFun := EnvelopingBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (EnvelopingBimodule k R M) := (coordinates M).addCommGroup
instance instModuleTensorProductMulOpposite : Module (R ⊗[k] Rᵐᵒᵖ) (EnvelopingBimodule k R M) :=
  (coordinates M).addEquiv.module (R ⊗[k] Rᵐᵒᵖ)
instance instModule : Module R (EnvelopingBimodule k R M) :=
  Module.compHom _ (tensorLeftInclusion k R Rᵐᵒᵖ)
instance instModuleMulOpposite : Module Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  Module.compHom _ (tensorRightInclusion k R Rᵐᵒᵖ)

@[simp] theorem value_zero : (0 : EnvelopingBimodule k R M).value = 0 := rfl
@[simp] theorem value_add (x y : EnvelopingBimodule k R M) :
    (x + y).value = x.value + y.value := rfl
@[simp] theorem value_smul (a : R ⊗[k] Rᵐᵒᵖ) (x : EnvelopingBimodule k R M) :
    (a • x).value = a • x.value := rfl
@[simp] theorem value_left_smul (a : R) (x : EnvelopingBimodule k R M) :
    (a • x).value = (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x.value := rfl
@[simp] theorem value_right_smul (b : Rᵐᵒᵖ) (x : EnvelopingBimodule k R M) :
    (b • x).value = ((1 : R) ⊗ₜ[k] b) • x.value := rfl

instance instSMulCommClassMulOpposite : SMulCommClass R Rᵐᵒᵖ (EnvelopingBimodule k R M) where
  smul_comm a b x := by
    ext
    change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • x.value) =
      ((1 : R) ⊗ₜ[k] b) • ((a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x.value)
    simp only [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable [Module k M]

instance instModule_1 : Module k (EnvelopingBimodule k R M) := (coordinates M).addEquiv.module k

@[simp] theorem value_scalar_smul (a : k) (x : EnvelopingBimodule k R M) :
    (a • x).value = a • x.value := rfl

def scalarEquiv : EnvelopingBimodule k R M ≃ₗ[k] M := (coordinates M).addEquiv.linearEquiv k

instance instFiniteOfCarrierTensorProductMulOpposite [Module.Finite k M] : Module.Finite k (EnvelopingBimodule k R M) :=
  Module.Finite.equiv (scalarEquiv M).symm

variable [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]

instance instIsScalarTower : IsScalarTower k R (EnvelopingBimodule k R M) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    ext
    change ((algebraMap k R a) ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x.value = a • x.value
    exact IsScalarTower.algebraMap_smul (R ⊗[k] Rᵐᵒᵖ) a x.value

instance instIsScalarTowerMulOpposite : IsScalarTower k Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    ext
    change ((1 : R) ⊗ₜ[k] (algebraMap k Rᵐᵒᵖ a)) • x.value = a • x.value
    rw [show (1 : R) ⊗ₜ[k] algebraMap k Rᵐᵒᵖ a = algebraMap k (R ⊗[k] Rᵐᵒᵖ) a from
      (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] R ⊗[k] Rᵐᵒᵖ).commutes a]
    exact IsScalarTower.algebraMap_smul (R ⊗[k] Rᵐᵒᵖ) a x.value

instance instSMulCommClass : SMulCommClass k R (EnvelopingBimodule k R M) where
  smul_comm a r x := by
    simp only [← IsScalarTower.algebraMap_smul R a, ← mul_smul, Algebra.commutes]

end EnvelopingBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {M N P : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k P] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) P]

def map (f : M ⟶ N) : EnvelopingBimodule k R M →ₗ[k] EnvelopingBimodule k R N where
  toFun x := ⟨f.hom x.value⟩
  map_add' x y := by
    ext
    exact f.hom.map_add x.value y.value
  map_smul' c x := by
    ext
    exact (f.hom.restrictScalars k).map_smul c x.value

@[simp] theorem map_value (f : M ⟶ N) (x : EnvelopingBimodule k R M) :
    (map f x).value = f.hom x.value := rfl

@[simp] theorem map_left_smul (f : M ⟶ N) (a : R)
    (x : EnvelopingBimodule k R M) : map f (a • x) = a • map f x := by
  ext
  exact f.hom.map_smul (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) x.value

@[simp] theorem map_right_smul (f : M ⟶ N) (b : Rᵐᵒᵖ)
    (x : EnvelopingBimodule k R M) : map f (b • x) = b • map f x := by
  ext
  exact f.hom.map_smul ((1 : R) ⊗ₜ[k] b) x.value

@[simp] theorem map_id : map (𝟙 M) = LinearMap.id := by
  ext x
  rfl

@[simp] theorem map_comp (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = (map g).comp (map f) := by
  ext x
  rfl

@[simp] theorem map_zero : map (0 : M ⟶ N) = 0 := by
  ext x
  rfl

@[simp] theorem map_add (f g : M ⟶ N) : map (f + g) = map f + map g := by
  ext x
  rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

abbrev regularObject : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) :=
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (R ⊗[k] Rᵐᵒᵖ)

def unopAction : Rᵐᵒᵖ →ₗ[k] X →ₗ[k] X where
  toFun b :=
    { toFun := fun x => b.unop • x
      map_add' := smul_add b.unop
      map_smul' := by intros; exact smul_comm _ _ _ }
  map_add' b c := by ext x; exact add_smul b.unop c.unop x
  map_smul' c b := by
    ext x
    change (c • b.unop) • x = c • (b.unop • x)
    exact smul_assoc c b.unop x

def regularRaw : (R ⊗[k] Rᵐᵒᵖ) →ₗ[k] X →ₗ[k] (R ⊗[k] X) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => (TensorProduct.mk k R X a).comp (unopAction k R X b)
          map_add' := by intros; ext x; simp [unopAction, add_smul, TensorProduct.tmul_add]
          map_smul' := by intros; ext x; simp [unopAction] }
      map_add' := by intros; ext b x; simp
      map_smul' := by intros; ext b x; simp }

@[simp] theorem regularRaw_tmul (a : R) (b : Rᵐᵒᵖ) (x : X) :
    regularRaw k R X (a ⊗ₜ[k] b) x = a ⊗ₜ[k] (b.unop • x) := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

instance finitePiProjective {V : Type u} [AddCommGroup V] [Module R V]
    [Module.Projective R V] (n : ℕ) : Module.Projective R (Fin n → V) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : Fin n, V) ≃ₗ[R] (Fin n → V))

variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]

abbrev piObject (n : ℕ) : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) :=
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (Fin n → M)

def piProjection (n : ℕ) (i : Fin n) : piObject M n ⟶ M :=
  ModuleCat.ofHom (LinearMap.proj i)

def piInclusion (n : ℕ) (i : Fin n) : M ⟶ piObject M n :=
  ModuleCat.ofHom (LinearMap.single (R ⊗[k] Rᵐᵒᵖ) (fun _ : Fin n => M) i)

end ArExplicit.EnvelopingBimodule

end

end OAI
end


