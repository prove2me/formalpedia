-- Prove2me | Definitions.Def_OAIQ031A026
-- name    : OAIQ031A026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:03:08.859563+00:00
-- url     : https://prove2.me/theorems/4deffb2e-09d1-4a79-bd20-bc1015bacc16
-- title:
--   Definitions bundle OAIQ031A026 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 11 definitions, 2 instances and 23 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.liftLeft`, `OAI.ArExplicit.BalancedTensor.map`, `OAI.ArExplicit.BalancedTensor.mapFirst`, `OAI.ArExplicit.BalancedTensor.relationsAsLeft`, `OAI.ArExplicit.EnvelopingBimodule.mapRight`, `OAI.ArExplicit.EnvelopingBimodule.regularBilinear`, `OAI.ArExplicit.EnvelopingBimodule.regularEvaluation`, `OAI.ArExplicit.EnvelopingBimodule.regularInclusion`, `OAI.ArExplicit.EnvelopingBimodule.regularInverse`, `OAI.ArExplicit.EnvelopingBimodule.tensorMap`, `OAI.ArExplicit.FiniteLeftModule.canonicalFreeCoverMap`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Fibers_FiniteModuleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteModuleFiber.lean), [`AuslanderReiten_Stable_StableHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHom.lean), [`AuslanderReiten_Tensor_BalancedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensor.lean), [`AuslanderReiten_Tensor_BalancedTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorAction.lean), [`AuslanderReiten_Tensor_BalancedTensorFirst`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorFirst.lean), [`AuslanderReiten_Tensor_BalancedTensorMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorMap.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedExact.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedMap.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedRegular.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001` and `OAIQ031A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A044`, `OAIQ031A045`, `OAIQ031A049`, `OAIQ031A050`, `OAIQ031A052`, `OAIQ031A053`, `OAIQ031A054` and `OAIQ031A055`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002

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

theorem simpleCoordinate_surjective : Function.Surjective (simpleCoordinate q) := by
  intro r
  refine ⟨Submodule.Quotient.mk (r • vertexF q), ?_⟩
  simp [vertexF]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteModuleFiber
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def canonicalFreeCoverMap (Y : FiniteLeftModule k R) : Y.canonicalFreeCover.carrier ⟶ Y.carrier :=
  ModuleCat.ofHom
    { __ := (freeCoverMapScalar Y).toAddHom
      map_smul' r z := by
        change freeCoverMapScalar Y (r • z) = r • freeCoverMapScalar Y z
        induction z using OAI.tensorInductionOn with
        | add x y hx hy => simp [smul_add, hx, hy]
        | tmul s y => exact mul_smul r s y }

@[simp] theorem canonicalFreeCoverMap_tmul (Y : FiniteLeftModule k R) (r : R) (y : Y.carrier) :
    Y.canonicalFreeCoverMap.hom (r ⊗ₜ[k] y) = r • y := rfl

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHom
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace ArExplicit

variable (R : Type u) [Ring R]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

variable {R M N}

variable {L P : Type u} [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]

variable (R M N)

namespace StableHom

variable {R M N}

theorem classOf_surjective : Function.Surjective (classOf R M N) :=
  QuotientAddGroup.mk'_surjective _

end StableHom

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensor
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

namespace BalancedTensor

variable {k R F M}

variable {N : Type*} [AddCommGroup N] [Module k N]

@[ext] theorem hom_ext (f g : BalancedTensor k R F M →ₗ[k] N)
    (h : ∀ x y, f (tmul x y) = g (tmul x y)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
      induction z using OAI.tensorInductionOn with
      | tmul x y => exact h x y
      | add z z' hz hz' =>
          change f ((balancingRelations k R F M).mkQ (z + z')) =
            g ((balancingRelations k R F M).mkQ (z + z'))
          simp only [map_add]
          exact congrArg₂ (· + ·) hz hz'

end BalancedTensor
end ArExplicit

end OAI
end

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

theorem smul_mem_relations (s : S) {z : F ⊗[k] M}
    (hz : z ∈ balancingRelations k R F M) : s • z ∈ balancingRelations k R F M := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨f, r, m, rfl⟩ := hz
      rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_comm s]
      exact Submodule.subset_span ⟨s • f, r, m, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [smul_add] using (balancingRelations k R F M).add_mem ihx ihy
  | smul c z hz ih =>
      rw [← smul_comm c s z]
      exact (balancingRelations k R F M).smul_mem c ih

def relationsAsLeft : Submodule S (F ⊗[k] M) where
  __ := (balancingRelations k R F M).toAddSubmonoid
  smul_mem' := fun s _ hz => smul_mem_relations s hz

instance (priority := 100) instModule : Module S (BalancedTensor k R F M) :=
  Submodule.Quotient.module (relationsAsLeft (k := k) (R := R) (S := S) (F := F) (M := M))

@[simp] theorem smul_tmul (s : S) (f : F) (m : M) :
    s • tmul (k := k) (R := R) f m = tmul (s • f) m := rfl

variable [Algebra k S] [IsScalarTower k S F]

instance instIsScalarTower : IsScalarTower k S (BalancedTensor k R F M) where
  smul_assoc c s z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
        change Submodule.Quotient.mk ((c • s) • z) =
          (Submodule.Quotient.mk (c • s • z) : BalancedTensor k R F M)
        rw [smul_assoc]

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorMap
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

open TensorProduct

variable {k R F M N : Type*} [CommRing k] [Ring R]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]

@[elab_as_elim] theorem induction_on {motive : BalancedTensor k R F M → Prop}
    (z : BalancedTensor k R F M) (zero : motive 0)
    (tmul : ∀ f m, motive (tmul f m))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  classical
  by_cases hz : z = 0
  · simpa only [hz] using zero
  clear hz
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    induction z using OAI.tensorInductionOn with
    | tmul f m => exact tmul f m
    | add x y hx hy => exact add _ _ hx hy

variable {F' M' : Type*} [AddCommGroup F'] [AddCommGroup M']
variable [Module k F'] [Module k M'] [Module Rᵐᵒᵖ F'] [Module R M']

def map (a : F →ₗ[k] F') (b : M →ₗ[k] M')
    (ha : ∀ (r : Rᵐᵒᵖ) f, a (r • f) = r • a f)
    (hb : ∀ (r : R) m, b (r • m) = r • b m) :
    BalancedTensor k R F M →ₗ[k] BalancedTensor k R F' M' :=
  lift
    { toFun := fun f => (mk (a f)).comp b
      map_add' := by intros; ext m; simp
      map_smul' := by intros; ext m; simp }
    (by
      intro f r m
      change tmul (a (MulOpposite.op r • f)) (b m) = tmul (a f) (b (r • m))
      rw [ha, hb, balance])

@[simp] theorem map_tmul (a : F →ₗ[k] F') (b : M →ₗ[k] M')
    (ha : ∀ (r : Rᵐᵒᵖ) f, a (r • f) = r • a f)
    (hb : ∀ (r : R) m, b (r • m) = r • b m) (f : F) (m : M) :
    map a b ha hb (tmul f m) = tmul (a f) (b m) := rfl

section LeftLinear

variable {S : Type*} [Ring S] [AddCommGroup N] [Module k N]
variable [Module S F] [Module S N]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

def liftLeft (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m))
    (hs : ∀ (s : S) f m, b (s • f) m = s • b f m) :
    BalancedTensor k R F M →ₗ[S] N where
  __ := (lift b hb).toAddHom
  map_smul' s z := by
    change lift b hb (s • z) = s • lift b hb z
    induction z using induction_on with
    | zero => simp
    | tmul f m => simpa only [smul_tmul, lift_tmul, RingHom.id_apply] using hs s f m
    | add x y hx hy => simp only [smul_add, map_add] at *; rw [hx, hy]

@[simp] theorem liftLeft_tmul (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m))
    (hs : ∀ (s : S) f m, b (s • f) m = s • b f m) (f : F) (m : M) :
    liftLeft b hb hs (tmul f m) = b f m := rfl

end LeftLinear

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFirst
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

universe u
variable {k R F G Q X : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup Q] [Module k Q] [Module Rᵐᵒᵖ Q] [IsScalarTower k Rᵐᵒᵖ Q]
variable [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]

def mapFirst (X : Type u) [AddCommGroup X] [Module k X] [Module R X]
    (f : F →ₗ[Rᵐᵒᵖ] G) : BalancedTensor k R F X →ₗ[k] BalancedTensor k R G X :=
  map (f.restrictScalars k) (LinearMap.id : X →ₗ[k] X)
    (fun a x => f.map_smul a x) (fun _ _ => rfl)

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_tmul (f : F →ₗ[Rᵐᵒᵖ] G) (m : F) (x : X) :
    mapFirst (k := k) X f (tmul m x) = tmul (f m) x := rfl

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_id : mapFirst (k := k) X (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => rfl
  | add z w hz hw => simp_all

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_comp (f : F →ₗ[Rᵐᵒᵖ] G) (g : G →ₗ[Rᵐᵒᵖ] Q) :
    mapFirst (k := k) X (g.comp f) = (mapFirst (k := k) X g).comp (mapFirst (k := k) X f) := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => rfl
  | add z w hz hw => simp_all

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_add (f g : F →ₗ[Rᵐᵒᵖ] G) :
    mapFirst (k := k) X (f + g) = mapFirst (k := k) X f + mapFirst (k := k) X g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => simp [BalancedTensor.add_tmul]
  | add z w hz hw => simp_all [add_left_comm, add_comm]

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_zero : mapFirst (k := k) X (0 : F →ₗ[Rᵐᵒᵖ] G) = 0 := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => simp
  | add z w hz hw => simp_all

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedMap
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

def tensorMap (f : M ⟶ N) :
    BalancedTensor k R (EnvelopingBimodule k R M) X →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R N) X where
  __ := (BalancedTensor.map (map f) (LinearMap.id : X →ₗ[k] X)
    (map_right_smul f) (fun _ _ => rfl)).toAddHom
  map_smul' a z := by
    change BalancedTensor.map (map f) (LinearMap.id : X →ₗ[k] X)
      (map_right_smul f) (fun _ _ => rfl) (a • z) =
        a • BalancedTensor.map (map f) (LinearMap.id : X →ₗ[k] X)
          (map_right_smul f) (fun _ _ => rfl) z
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | tmul m x => simp only [BalancedTensor.smul_tmul, BalancedTensor.map_tmul,
        LinearMap.id_apply, map_left_smul]
    | add z w hz hw => simp_all

omit [IsScalarTower k R X]

@[simp] theorem tensorMap_tmul (f : M ⟶ N)
    (m : EnvelopingBimodule k R M) (x : X) :
    tensorMap X f (BalancedTensor.tmul m x) = BalancedTensor.tmul (map f m) x := rfl

@[simp] theorem tensorMap_id : tensorMap X (𝟙 M) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => rfl
  | add z w hz hw => simp_all

@[simp] theorem tensorMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    tensorMap X (f ≫ g) = (tensorMap X g).comp (tensorMap X f) := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => rfl
  | add z w hz hw => simp_all

@[simp] theorem tensorMap_zero : tensorMap X (0 : M ⟶ N) = 0 := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => simp
  | add z w hz hw => simp_all

@[simp] theorem tensorMap_add (f g : M ⟶ N) :
    tensorMap X (f + g) = tensorMap X f + tensorMap X g := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul m x => simp [BalancedTensor.add_tmul]
  | add z w hz hw =>
    simp only [_root_.LinearMap.map_add, hz, hw]

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedExact
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {M N Q : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k Q] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q]

def mapRight (f : M ⟶ N) :
    EnvelopingBimodule k R M →ₗ[Rᵐᵒᵖ] EnvelopingBimodule k R N where
  toFun := map f
  map_add' := (map f).map_add
  map_smul' := map_right_smul f

variable (X : ModuleCat.{u} R) [Module k X]

@[simp] theorem mapFirst_mapRight_apply (f : M ⟶ N)
    (z : BalancedTensor k R (EnvelopingBimodule k R M) X) :
    BalancedTensor.mapFirst X (mapRight f) z = tensorMap X f z := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedRegular
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def regularBilinear : EnvelopingBimodule k R (regularObject k R) →ₗ[k]
    X →ₗ[k] (R ⊗[k] X) :=
  (regularRaw k R X).comp (scalarEquiv (regularObject k R)).toLinearMap

theorem regularBilinear_balance
    (f : EnvelopingBimodule k R (regularObject k R)) (r : R) (x : X) :
    regularBilinear k R X (MulOpposite.op r • f) x =
      regularBilinear k R X f (r • x) := by
  rcases f with ⟨f⟩
  induction f using OAI.tensorInductionOn with
  | add f g hf hg =>
    change regularRaw k R X (((1 : R) ⊗ₜ[k] MulOpposite.op r) * (f + g)) x =
      regularRaw k R X (f + g) (r • x)
    simp only [mul_add, _root_.map_add, LinearMap.add_apply] at *
    exact congrArg₂ (· + ·) hf hg
  | tmul a b =>
    change regularRaw k R X (((1 : R) ⊗ₜ[k] MulOpposite.op r) * (a ⊗ₜ[k] b)) x =
      regularRaw k R X (a ⊗ₜ[k] b) (r • x)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, regularRaw_tmul,
      MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul]

theorem regularBilinear_left
    (r : R) (f : EnvelopingBimodule k R (regularObject k R)) (x : X) :
    regularBilinear k R X (r • f) x = r • regularBilinear k R X f x := by
  rcases f with ⟨f⟩
  induction f using OAI.tensorInductionOn with
  | add f g hf hg =>
    change regularRaw k R X ((r ⊗ₜ[k] (1 : Rᵐᵒᵖ)) * (f + g)) x =
      r • regularRaw k R X (f + g) x
    simp only [mul_add, _root_.map_add, LinearMap.add_apply, smul_add] at *
    exact congrArg₂ (· + ·) hf hg
  | tmul a b =>
    change regularRaw k R X ((r ⊗ₜ[k] (1 : Rᵐᵒᵖ)) * (a ⊗ₜ[k] b)) x =
      r • regularRaw k R X (a ⊗ₜ[k] b) x
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, regularRaw_tmul,
      TensorProduct.smul_tmul', smul_eq_mul]

def regularEvaluation :
    BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X →ₗ[R]
      R ⊗[k] X :=
  BalancedTensor.liftLeft (regularBilinear k R X)
    (regularBilinear_balance k R X) (regularBilinear_left k R X)

@[simp] theorem regularEvaluation_tmul (a : R) (b : Rᵐᵒᵖ) (x : X) :
    regularEvaluation k R X (BalancedTensor.tmul ⟨a ⊗ₜ[k] b⟩ x) =
      a ⊗ₜ[k] (b.unop • x) := rfl

def regularInclusion : R →ₗ[k] EnvelopingBimodule k R (regularObject k R) where
  toFun a := ⟨a ⊗ₜ[k] (1 : Rᵐᵒᵖ)⟩
  map_add' a b := by ext; exact TensorProduct.add_tmul a b 1
  map_smul' c a := by ext; exact TensorProduct.smul_tmul' c a 1

def regularInverse : R ⊗[k] X →ₗ[k]
    BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X :=
  TensorProduct.lift ((BalancedTensor.mk (k := k) (R := R)).comp (regularInclusion k R))

end ArExplicit.EnvelopingBimodule

end

end OAI
end


