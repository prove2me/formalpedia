-- Prove2me | Definitions.Def_OAIQ031A070
-- name    : OAIQ031A070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:15:57.432727+00:00
-- url     : https://prove2.me/theorems/667998b2-0f6e-4599-aabd-6d6e15d6ec2e
-- title:
--   Definitions bundle OAIQ031A070 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 2 definitions, 2 instances and 3 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.equiv`, `OAI.ArExplicit.barZeroScalarEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarTensorRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarTensorRegular.lean), [`AuslanderReiten_Ext_ExtFunctorScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtFunctorScalar.lean), [`AuslanderReiten_Homology_NatComparisonFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/NatComparisonFunctor.lean), [`AuslanderReiten_Tensor_BalancedTensorLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorLinear.lean), [`AuslanderReiten_Tensor_EnvelopingEvaluationFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingEvaluationFunctor.lean), [`AuslanderReiten_Tensor_ExternalBalancedEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedEquiv.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A045`, `OAIQ031A049`, `OAIQ031A050`, `OAIQ031A053` and `OAIQ031A054` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A085`, `OAIQ031A086` and `OAIQ031A087`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A050
import Definitions.Def_OAIQ031A053
import Definitions.Def_OAIQ031A054

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarTensorRegular
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def barZeroScalarEquiv : AbsoluteBar.moduleObject k A 0 ≃ₗ[k] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change AbsoluteBar.representation k A 0 (algebraMap k (AbsoluteBar.Enveloping k A) a)
      (show A from x) = a • (show A from x)
    rw [AlgHom.commutes]
    rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtFunctorScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {X Y : C} (e : X ≅ Y) (E : Y ≅ F.obj Y)

theorem exactFunctor_scalar_transport (n : ℕ) (c : k)
    (h : ∀ z : Ext Y Y n, selfExtIso (k := k) E.symm n (z.mapExactFunctor F) = c • z)
    (x : Ext X X n) :
    selfExtIso (k := k) (e ≪≫ E ≪≫ F.mapIso e.symm).symm n (x.mapExactFunctor F) = c • x := by
  have ht := selfExtIso_conjugated_functor (k := k) F e.symm E n x
  simp only [Iso.symm_symm_eq] at ht
  rw [← ht, h, map_smul]
  congr 1
  simp [selfExtIso_apply]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_NatComparisonFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

theorem natComparisonEndExt_map (e : Y ≅ F.obj X)
    (φ : ProjectiveResolution.Hom Q (mapResolution F P) e.hom) (r : ℕ)
    (f : ∀ n, P.complex.X (r+n) ⟶ P.complex.X n)
    (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n = P.complex.d (r+(n+1)) (r+n) ≫ f n)
    (g : ∀ n, Q.complex.X (r+n) ⟶ Q.complex.X n)
    (hg : ∀ n, g (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (r+(n+1)) (r+n) ≫ g n)
    (ha : natComparisonAugmentation Q r g =
      (φ.hom.f r ≫ F.map (natComparisonAugmentation P r f)) ≫ e.inv) :
    endExt Q (natComparisonCocycle (k := k) Q Q r g hg) =
      ((Ext.mk₀ e.hom).comp
        ((endExt P (natComparisonCocycle (k := k) P P r f hf)).mapExactFunctor F) (zero_add r)).comp
          (Ext.mk₀ e.inv) (add_zero r) := by
  rw [natComparison_endExt_eq, natComparison_endExt_eq]
  exact (map_extMk_comparison F P Q e φ
    (natComparisonAugmentation P r f) (natComparison_augmented_cycle P r f hf)
    (natComparisonAugmentation Q r g) (natComparison_augmented_cycle Q r g hg) ha).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorLinear
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
  [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
  [IsScalarTower k Rᵐᵒᵖ F] [IsScalarTower k S F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

instance functor_linear :
    (functor (k := k) (R := R) (S := S) (F := F)).Linear k where
  map_smul := by
    intro M N g a
    apply ModuleCat.hom_ext
    apply leftHom_ext
    intro f m
    change tmul (k := k) (R := R) f ((algebraMap k R a) • g.hom m) =
      (algebraMap k S a) • tmul (k := k) (R := R) f (g.hom m)
    rw [IsScalarTower.algebraMap_smul R a (g.hom m),
      IsScalarTower.algebraMap_smul S a (tmul (k := k) (R := R) f (g.hom m))]
    exact map_smul (mk (k := k) (R := R) f) a (g.hom m)

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingEvaluationFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance instAdditiveModuleCatTensorProductMulOppositeEvaluationFunctor : (evaluationFunctor k R X).Additive where
  map_add := by intro M N f g; apply ModuleCat.hom_ext; exact tensorMap_add X f g

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def equiv : Sbal ≃ₗ[k] Lbal ⊗[k] Rbal where
  __ := forward e v he hv
  invFun := inverse e v he hv
  left_inv := inverse_forward e v he hv
  right_inv := forward_inverse e v he hv

@[simp] theorem equiv_pure (f : F) (g : G) (x : X) (y : Y) :
    equiv e v he hv (BalancedTensor.tmul (e.symm (f ⊗ₜ[k] g)) (v.symm (x ⊗ₜ[k] y))) =
      BalancedTensor.tmul (R := A) f x ⊗ₜ[k] BalancedTensor.tmul (R := B) g y :=
  forward_pure e v he hv f g x y

end ArExplicit.ExternalBalanced

end

end OAI
end


