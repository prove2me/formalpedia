-- Prove2me | Definitions.Def_OAIQ031A049
-- name    : OAIQ031A049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:05:56.013398+00:00
-- url     : https://prove2.me/theorems/1fcb1183-af37-42c5-938e-d4b1169b0f86
-- title:
--   Definitions bundle OAIQ031A049 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 17 definitions, 1 instance and 23 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.freeRecombine`, `OAI.ArExplicit.BalancedTensor.functor`, `OAI.ArExplicit.BalancedTensor.leftCoefficients`, `OAI.ArExplicit.BalancedTensor.leftRecombine`, `OAI.ArExplicit.BalancedTensor.mapLeft`, `OAI.ArExplicit.BalancedTensor.mapLeftLinear`, `OAI.ArExplicit.BalancedTensor.mapRight`, `OAI.ArExplicit.BalancedTensor.piRightMap`, `OAI.ArExplicit.BalancedTensor.rightCoefficients`, `OAI.ArExplicit.BalancedTensor.runit`, `OAI.ArExplicit.BalancedTensor.runitMap`, `OAI.ArExplicit.DualTensor.dualHomComplex`, `OAI.ArExplicit.DualTensor.dualHomDifferential`, `OAI.ArExplicit.DualTensor.dualHomObject`, `OAI.ArExplicit.DualTensor.evaluation`, `OAI.ArExplicit.DualTensor.inverseUsing`, `OAI.ArExplicit.DualTensor.moduleEvaluation`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Duality_DualTensorComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorComplex.lean), [`AuslanderReiten_Duality_DualTensorEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorEvaluation.lean), [`AuslanderReiten_Duality_DualTensorModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorModule.lean), [`AuslanderReiten_Tensor_BalancedTensorCategory`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCategory.lean), [`AuslanderReiten_Tensor_BalancedTensorExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorExact.lean), [`AuslanderReiten_Tensor_BalancedTensorFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorFunctor.lean), [`AuslanderReiten_Tensor_BalancedTensorLeftExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorLeftExact.lean), [`AuslanderReiten_Tensor_BalancedTensorPi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorPi.lean), [`AuslanderReiten_Tensor_BalancedTensorUnit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorUnit.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A026`, `OAIQ031A031` and `OAIQ031A032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A065`, `OAIQ031A066`, `OAIQ031A067`, `OAIQ031A068`, `OAIQ031A069`, `OAIQ031A070`, `OAIQ031A071`, `OAIQ031A073`, `OAIQ031A075` and `OAIQ031A076`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A032

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem smul_vertexE (a : E q) : (a : C) • vertexE q = a := by
  apply Subtype.ext
  exact a.property

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def mapRight (b : M →ₗ[R] N) : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F N :=
  liftLeft
    { toFun := fun f => (mk f).comp (b.restrictScalars k)
      map_add' := by intros; ext m; simp
      map_smul' := by intros; ext m; simp }
    (by
      intro f r m
      change tmul (MulOpposite.op r • f) (b m) = tmul f (b (r • m))
      rw [b.map_smul, balance])
    (by intro s f m; exact (smul_tmul s f (b m)).symm)

@[simp] theorem mapRight_tmul (b : M →ₗ[R] N) (f : F) (m : M) :
    mapRight (k := k) (S := S) b (tmul f m) = tmul f (b m) := rfl

omit [Algebra k R] [IsScalarTower k R M] in
@[ext] theorem leftHom_ext {Q : Type*} [AddCommGroup Q] [Module S Q]
    (f g : BalancedTensor k R F M →ₗ[S] Q)
    (h : ∀ x y, f (tmul x y) = g (tmul x y)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul x y => exact h x y
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem mapRight_id : mapRight (k := k) (S := S) (LinearMap.id : M →ₗ[R] M) =
    (LinearMap.id : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F M) := by
  apply leftHom_ext
  intro f m
  rfl

@[simp] theorem mapRight_comp (b : M →ₗ[R] N) (c : N →ₗ[R] L) :
    mapRight (k := k) (F := F) (S := S) (c.comp b) = (mapRight c).comp (mapRight b) := by
  apply leftHom_ext
  intro f m
  rfl

@[simp] theorem mapRight_zero : mapRight (k := k) (S := S) (0 : M →ₗ[R] N) =
    (0 : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F N) := by
  apply leftHom_ext
  intro f m
  exact tmul_zero f

theorem mapRight_add (b c : M →ₗ[R] N) :
    mapRight (k := k) (F := F) (S := S) (b + c) = mapRight b + mapRight c := by
  apply leftHom_ext
  intro f m
  exact tmul_add f (b m) (c m)

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorPi
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Algebra k R] [Ring S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def piRightMap : BalancedTensor k R F (ι → M) →ₗ[S] (ι → BalancedTensor k R F M) :=
  LinearMap.pi fun i => mapRight (k := k) (S := S) (LinearMap.proj i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem piRightMap_tmul (f : F) (m : ι → M) (i : ι) :
    piRightMap (S := S) (tmul f m : BalancedTensor k R F (ι → M)) i = tmul f (m i) := rfl

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorUnit
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

section Right

variable {F : Type*} [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]

def runitMap : BalancedTensor k R F R →ₗ[k] F :=
  lift rightAction (by
    intro f r s
    change MulOpposite.op s • MulOpposite.op r • f = MulOpposite.op (r * s) • f
    rw [MulOpposite.op_mul, mul_smul])

@[simp] theorem runitMap_tmul (f : F) (r : R) :
    runitMap (tmul f r : BalancedTensor k R F R) = MulOpposite.op r • f := rfl

def runit : BalancedTensor k R F R ≃ₗ[k] F where
  __ := runitMap (k := k) (R := R) (F := F)
  invFun f := tmul f 1
  right_inv f := by simp [runitMap_tmul]
  left_inv z := by
    change tmul (runitMap z) 1 = z
    induction z using induction_on with
    | zero => simp
    | tmul f r => simpa using (balance (k := k) (R := R) f r (1 : R))
    | add x y hx hy => simpa only [map_add, add_tmul] using congrArg₂ (· + ·) hx hy

@[simp] theorem runit_tmul (f : F) (r : R) :
    runit (tmul f r : BalancedTensor k R F R) = MulOpposite.op r • f := rfl

end Right

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
namespace DualTensor

variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

def evaluation : BalancedTensor k R (Coinduced k R) V →ₗ[k] Module.Dual k (V →ₗ[R] R) :=
  BalancedTensor.lift formula (by
    intro ℓ r v
    ext f
    change ℓ.functional (r * f v) = ℓ.functional (f (r • v))
    rw [f.map_smul, smul_eq_mul])

@[simp] theorem evaluation_tmul (ℓ : Coinduced k R) (v : V) (f : V →ₗ[R] R) :
    evaluation (BalancedTensor.tmul ℓ v) f = ℓ.functional (f v) := rfl

variable {n : ℕ}

def inverseUsing (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (φ : Module.Dual k (V →ₗ[R] R)) : BalancedTensor k R (Coinduced k R) V :=
  ∑ i, BalancedTensor.tmul (Coinduced.mk (φ.comp (coefficientRight s i))) (p (Pi.single i 1))

theorem evaluation_left (r : R)
    (z : BalancedTensor k R (Coinduced k R) V) (f : V →ₗ[R] R) :
    evaluation (r • z) f = evaluation z (MulOpposite.op r • f) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul ℓ v => rfl
  | add x y hx hy => simp only [smul_add, map_add, LinearMap.add_apply, hx, hy]

end DualTensor
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.DualTensor
variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
variable [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

def moduleEvaluation : BalancedTensor k R (Coinduced k R) V →ₗ[R]
    RightDual k R (V →ₗ[R] R) where
  toFun z := ⟨evaluation z⟩
  map_add' x y := by apply RightDual.ext; exact map_add evaluation x y
  map_smul' r z := by
    apply RightDual.ext
    ext f
    exact evaluation_left r z f

@[simp] theorem moduleEvaluation_tmul (φ : Coinduced k R) (v : V) (f : V →ₗ[R] R) :
    (moduleEvaluation (BalancedTensor.tmul φ v)).functional f = φ.functional (f v) := rfl

end ArExplicit.DualTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [SMulCommClass k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L] [SMulCommClass k R L]
variable {n : ℕ}

def rightCoefficients (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) :
    BalancedTensor k R F M →ₗ[k] (Fin n → M) :=
  lift
    { toFun f :=
        { toFun m i := (s f i).unop • m
          map_add' m m' := by ext i; exact smul_add _ _ _
          map_smul' c m := by ext i; exact (smul_comm c (s f i).unop m).symm }
      map_add' f f' := by
        ext m i
        change (s (f + f') i).unop • m = (s f i).unop • m + (s f' i).unop • m
        simp only [map_add, Pi.add_apply, MulOpposite.unop_add, add_smul]
      map_smul' c f := by
        ext m i
        change (s (c • f) i).unop • m = c • (s f i).unop • m
        simp only [LinearMap.map_smul_of_tower, Pi.smul_apply, MulOpposite.unop_smul,
          smul_assoc] }
    (by
      intro f r m
      ext i
      change (s (MulOpposite.op r • f) i).unop • m = (s f i).unop • (r • m)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, MulOpposite.unop_mul,
        MulOpposite.unop_op, mul_smul])

omit [SMulCommClass k Rᵐᵒᵖ F] in
@[simp] theorem rightCoefficients_tmul (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ))
    (f : F) (m : M) (i : Fin n) :
    rightCoefficients (k := k) s (tmul f m) i = (s f i).unop • m := rfl

def freeRecombine (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F) :
    (Fin n → M) →ₗ[k] BalancedTensor k R F M :=
  ∑ i, (mk (p (Pi.single i 1))).comp (LinearMap.proj i)

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
  [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem freeRecombine_apply (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F) (m : Fin n → M) :
    freeRecombine (k := k) p m = ∑ i, tmul (p (Pi.single i 1)) (m i) := by
  simp [freeRecombine, mk]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorLeftExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable {F G H M : Type*}
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup H] [Module k H] [Module Rᵐᵒᵖ H] [IsScalarTower k Rᵐᵒᵖ H]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

def mapLeft (a : F →ₗ[Rᵐᵒᵖ] G) : BalancedTensor k R F M →ₗ[k] BalancedTensor k R G M :=
  map (a.restrictScalars k) LinearMap.id (fun r f => a.map_smul r f) (fun _ _ => rfl)

omit [IsScalarTower k R M] in
@[simp] theorem mapLeft_tmul (a : F →ₗ[Rᵐᵒᵖ] G) (f : F) (m : M) :
    mapLeft (k := k) a (tmul f m) = tmul (a f) m := rfl

omit [IsScalarTower k R M] in
@[simp] theorem mapLeft_comp (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H) :
    mapLeft (k := k) (M := M) (b.comp a) = (mapLeft b).comp (mapLeft a) := by
  apply hom_ext
  intro f m
  rfl

omit [IsScalarTower k R M] in
@[simp] theorem mapLeft_zero : mapLeft (k := k) (M := M) (0 : F →ₗ[Rᵐᵒᵖ] G) = 0 := by
  apply hom_ext
  intro f m
  exact zero_tmul m

variable {n : ℕ}

def leftCoefficients (s : M →ₗ[R] (Fin n → R)) :
    BalancedTensor k R F M →ₗ[k] (Fin n → F) :=
  lift
    { toFun f :=
        { toFun m i := MulOpposite.op (s m i) • f
          map_add' m m' := by
            ext i
            simp only [map_add, Pi.add_apply, MulOpposite.op_add, add_smul]
          map_smul' c m := by
            ext i
            simp only [LinearMap.map_smul_of_tower, Pi.smul_apply, MulOpposite.op_smul,
              smul_assoc, RingHom.id_apply] }
      map_add' f f' := by ext m i; exact smul_add _ _ _
      map_smul' c f := by
        ext m i
        exact (smul_comm c (MulOpposite.op (s m i)) f).symm }
    (by
      intro f r m
      ext i
      change MulOpposite.op (s m i) • (MulOpposite.op r • f) = MulOpposite.op (s (r • m) i) • f
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, MulOpposite.op_mul, mul_smul])

@[simp] theorem leftCoefficients_tmul (s : M →ₗ[R] (Fin n → R)) (f : F) (m : M) (i : Fin n) :
    leftCoefficients (k := k) s (tmul f m) i = MulOpposite.op (s m i) • f := rfl

def leftRecombine (p : (Fin n → R) →ₗ[R] M) :
    (Fin n → F) →ₗ[k] BalancedTensor k R F M :=
  ∑ i, (((mk (k := k) (R := R)).flip (p (Pi.single i 1))).comp (LinearMap.proj i))

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ F] [IsScalarTower k R M] in
@[simp] theorem leftRecombine_apply (p : (Fin n → R) →ₗ[R] M) (f : Fin n → F) :
    leftRecombine (k := k) p f = ∑ i, tmul (f i) (p (Pi.single i 1)) := by
  simp [leftRecombine, mk]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCategory
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.BalancedTensor
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable {k R S : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable {F G H : Type u}
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
  [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module S G]
  [SMulCommClass k S G] [SMulCommClass S Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup H] [Module k H] [Module Rᵐᵒᵖ H] [Module S H]
  [SMulCommClass k S H] [SMulCommClass S Rᵐᵒᵖ H] [IsScalarTower k Rᵐᵒᵖ H]

def mapLeftLinear (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f)
    (M : ModuleCat.{u} R) : BalancedTensor k R F M →ₗ[S] BalancedTensor k R G M where
  __ := (mapLeft (k := k) (M := M) a).toAddHom
  map_smul' s z := by
    change mapLeft (k := k) a (s • z) = s • mapLeft (k := k) a z
    induction z using induction_on with
    | zero => simp
    | tmul f m => simp only [smul_tmul, mapLeft_tmul, ha]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp] theorem mapLeftLinear_tmul (a : F →ₗ[Rᵐᵒᵖ] G)
    (ha : ∀ (s : S) f, a (s • f) = s • a f) (M : ModuleCat.{u} R) (f : F) (m : M) :
    mapLeftLinear (k := k) a ha M (tmul f m) = tmul (a f) m := rfl

def functor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (BalancedTensor k R F M)
  map a := ModuleCat.ofHom (mapRight (k := k) (F := F) (S := S) a.hom)
  map_id M := by apply ModuleCat.hom_ext; exact mapRight_id
  map_comp a b := by apply ModuleCat.hom_ext; exact mapRight_comp a.hom b.hom

instance instAdditiveModuleCatFunctor : (functor (k := k) (R := R) (S := S) (F := F)).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; exact mapRight_add _ _

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.DualTensor
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def dualHomObject (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (RightDual k R (P.X n →ₗ[R] R))

def dualHomDifferential (n : ℕ) :
    dualHomObject (k := k) P (n + 1) ⟶ dualHomObject (k := k) P n :=
  ModuleCat.ofHom (RightDual.map (precomposeRight (P.d (n + 1) n).hom))

theorem dualHomDifferential_comp (n : ℕ) :
    dualHomDifferential (k := k) P (n + 1) ≫ dualHomDifferential (k := k) P n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply RightDual.ext
  apply LinearMap.ext
  intro f
  change φ.functional ((f.comp (P.d (n + 1) n).hom).comp (P.d (n + 2) (n + 1)).hom) = 0
  have hd : (P.d (n + 1) n).hom.comp (P.d (n + 2) (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (P.d_comp_d (n + 2) (n + 1) n)
  rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero, map_zero]

def dualHomComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (dualHomObject (k := k) P) (dualHomDifferential (k := k) P)
    (dualHomDifferential_comp (k := k) P)

theorem dualHomComplex_d (n : ℕ) :
    (dualHomComplex (k := k) P).d (n + 1) n = dualHomDifferential (k := k) P n := by
  exact ChainComplex.of_d _ _ _

end ArExplicit.DualTensor

end

end OAI
end


