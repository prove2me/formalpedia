-- Prove2me | Definitions.Def_OAIQ031A099
-- name    : OAIQ031A099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:37:52.522383+00:00
-- url     : https://prove2.me/theorems/b23553a1-7f5f-4d41-8aff-92f30288491d
-- title:
--   Definitions bundle OAIQ031A099 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 3 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.EnvelopingBimodule.tensorProdEquiv`, `OAI.ArExplicit.ExternalBalanced.totalEndpointMap`, `OAI.ArExplicit.TwoCone.baseSuccessorEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeProjective.lean), [`AuslanderReiten_Ext_ExternalEvaluationAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationAugmentation.lean), [`AuslanderReiten_Ext_ExternalEvaluationDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationDifferential.lean), [`AuslanderReiten_Ext_ExternalEvaluationNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationNaturality.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedProduct.lean), [`AuslanderReiten_Tensor_ExternalBalancedHomExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedHomExt.lean), [`AuslanderReiten_Tensor_ExternalBalancedNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedNaturality.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A085`, `OAIQ031A086` and `OAIQ031A087` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A111`, `OAIQ031A112` and `OAIQ031A115`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A085
import Definitions.Def_OAIQ031A086
import Definitions.Def_OAIQ031A087

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)

def baseSuccessorEquiv (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    BaseCokernel D (n+1) ≃ₗ[R] LinearMap.ker (LinearMap.range (D.d n)).mkQ :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp (hex n)).symm).trans
    ((D.d n).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ (LinearMap.range (D.d n))).symm))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable {k A B : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

variable {M M' : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)}
  {N N' : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)} {X X' : ModuleCat.{u} A} {Y Y' : ModuleCat.{u} B}
  (f : M ⟶ M') (g : N ⟶ N') (h : X ⟶ X') (j : Y ⟶ Y')

theorem shuffle_natural :
    (shuffle k A B M' N' X' Y').toLinearMap.comp
      (balancedMap (exteriorMap f g) (ExternalTensor.mapHom k A B h j)) =
    (ExternalTensor.map k A B (balancedMap f h) (balancedMap g j)).comp
      (shuffle k A B M N X Y).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    obtain ⟨z, rfl⟩ := (bimoduleCoordinates k A B M N).symm.surjective z
    obtain ⟨w, rfl⟩ := (ExternalTensor.moduleScalarCoordinates k A B X Y).symm.surjective w
    induction z using OAI.tensorInductionOn with
    | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, hz, hz']
    | tmul m n =>
      induction w using OAI.tensorInductionOn with
      | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, hw, hw']
      | tmul x y =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, balancedMap_tmul,
          coordinates_map, scalarCoordinates_map, shuffle_pure, ExternalTensor.map_tmul]
        rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable {M M' : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)}
  {N N' : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)}

theorem balancedMap_identity {S : Type u} [Ring S] [Algebra k S]
    {L L' : ModuleCat.{u} (S ⊗[k] Sᵐᵒᵖ)} (Z : ModuleCat.{u} S) (f : L ⟶ L') :
    balancedMap f (𝟙 Z) = EnvelopingBimodule.tensorMap Z f := by
  unfold balancedMap
  change (BalancedTensor.mapRight (k := k) (S := S) (LinearMap.id : Z →ₗ[S] Z)).comp _ = _
  rw [BalancedTensor.mapRight_id, LinearMap.id_comp]

theorem shuffle_natural_fixed (f : M ⟶ M') (g : N ⟶ N') :
    (EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B)
      (ExternalTensor.moduleObject k A B X Y)).map (exteriorMap f g) ≫
        (shuffle k A B M' N' X Y).toModuleIso.hom =
    (shuffle k A B M N X Y).toModuleIso.hom ≫
      ExternalTensor.mapHom k A B
        ((EnvelopingBimodule.evaluationFunctor k A X).map f)
        ((EnvelopingBimodule.evaluationFunctor k B Y).map g) := by
  apply ModuleCat.hom_ext
  have h := shuffle_natural (k := k) f g (𝟙 X) (𝟙 Y)
  rw [ExternalTensor.mapHom_id, balancedMap_identity, balancedMap_identity,
    balancedMap_identity] at h
  exact h

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationDifferential
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y

theorem evaluatedTotal_hom_ext {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    {f g : (evaluatedTotal k A B X Y P Q).X n ⟶ N}
    (h : ∀ i j (hij : i+j=n), (E).map (ExternalTensor.inclusion k Ae Be P Q i j n hij) ≫ f =
      (E).map (ExternalTensor.inclusion k Ae Be P Q i j n hij) ≫ g) : f=g := by
  apply (isColimitOfHasCoproductOfPreservesColimit E
    (ExternalTensor.summands k Ae Be P Q n)).hom_ext
  rintro ⟨⟨⟨i,j⟩,hij⟩⟩
  exact h i j hij

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable {U : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)} {V : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)}
variable (P : ProjectiveResolution U) (Q : ProjectiveResolution V)
variable (P' : ProjectiveResolution X) (Q' : ProjectiveResolution Y)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "EA" => EnvelopingBimodule.evaluationFunctor k A X
local notation "EB" => EnvelopingBimodule.evaluationFunctor k B Y
local notation "E" => productEvaluation k A B X Y

def totalEndpointMap (e : (EA).obj U ⟶ X) (f : (EB).obj V ⟶ Y) :
    (E).obj (ExternalTensor.moduleObject k Ae Be U V) ⟶
      ExternalTensor.moduleObject k A B X Y :=
  (shuffle k A B U V X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B e f

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedProduct
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem tensorProd_left (z : EP) : tensorProdInv M N X (tensorProdMap M N X z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul m x =>
    change BalancedTensor.tmul (k := k) (R := R) (⟨(m.value.1, 0)⟩ : EnvelopingBimodule k R ProdMN) x +
      BalancedTensor.tmul (k := k) (R := R) (⟨(0, m.value.2)⟩ : EnvelopingBimodule k R ProdMN) x = _
    rw [← BalancedTensor.add_tmul]
    congr 1
    apply EnvelopingBimodule.ext
    simp

theorem tensorProd_right (z : EM × EN) : tensorProdMap M N X (tensorProdInv M N X z) = z := by
  rcases z with ⟨z, w⟩
  have hz : tensorProdMap M N X (tensorProdInv M N X (z, 0)) = (z, 0) := by
    induction z using BalancedTensor.induction_on with
    | zero =>
      change tensorProdMap M N X (tensorProdInv M N X 0) = 0
      rw [(tensorProdInv M N X).map_zero, (tensorProdMap M N X).map_zero]
    | add z z' hz hz' =>
      have hh : (z+z', (0 : EN)) = (z, 0) + (z', 0) := by simp
      rw [hh, _root_.map_add, _root_.map_add, hz, hz']
    | tmul m x =>
      change tensorProdMap M N X
        (BalancedTensor.tmul (k := k) (R := R) (⟨(m.value, 0)⟩ : EnvelopingBimodule k R ProdMN) x + 0) = _
      rw [add_zero, tensorProdMap_tmul]
      simp
      exact BalancedTensor.zero_tmul _
  have hw : tensorProdMap M N X (tensorProdInv M N X (0, w)) = (0, w) := by
    induction w using BalancedTensor.induction_on with
    | zero =>
      change tensorProdMap M N X (tensorProdInv M N X 0) = 0
      rw [(tensorProdInv M N X).map_zero, (tensorProdMap M N X).map_zero]
    | add w w' hw hw' =>
      have hh : ((0 : EM), w+w') = (0, w) + (0, w') := by simp
      rw [hh, _root_.map_add, _root_.map_add, hw, hw']
    | tmul n x =>
      change tensorProdMap M N X
        (0 + BalancedTensor.tmul (k := k) (R := R) (⟨(0, n.value)⟩ : EnvelopingBimodule k R ProdMN) x) = _
      rw [zero_add, tensorProdMap_tmul]
      simp
      exact BalancedTensor.zero_tmul _
  have hh : (z, w) = (z, (0 : EN)) + (0, w) := by simp
  rw [hh, _root_.map_add, _root_.map_add, hz, hw]

def tensorProdEquiv : EP ≃ₗ[R] EM × EN where
  __ := tensorProdMap M N X
  invFun := tensorProdInv M N X
  left_inv := tensorProd_left M N X
  right_inv := tensorProd_right M N X

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedHomExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B) (Z : ModuleCat.{u} (A ⊗[k] B))

theorem exterior_hom_ext
    (f g : (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶ Z)
    (h : ∀ (a : EnvelopingBimodule k A M) (b : EnvelopingBimodule k B N) (x : X) (y : Y),
      f (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      g (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  exact fourfold_add_hom_ext (k := k) (A := A) (B := B) (Z := Z)
    (bimoduleCoordinates k A B M N) (ExternalTensor.moduleScalarCoordinates k A B X Y)
    f.hom.toAddMonoidHom g.hom.toAddMonoidHom h

end ArExplicit.ExternalBalanced

end

end OAI
end


