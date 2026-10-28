-- Prove2me | Definitions.Def_OAIQ031A143
-- name    : OAIQ031A143
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:20:25.366013+00:00
-- url     : https://prove2.me/theorems/c2db4f0c-90fe-420e-b271-87e93200d39e
-- title:
--   Definitions bundle OAIQ031A143 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 8 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.eval`, `OAI.ArExplicit.ExternalBalanced.instModuleCarrierTensorProductCanonicalTensorObject`, `OAI.ArExplicit.ExternalBalanced.nativeTotalBarIso`, `OAI.ArExplicit.ExternalBalanced.totalFreeEvaluation`, `OAI.ArExplicit.ExternalTensor.homCochainEndExt`, `OAI.ArExplicit.ExternalTensor.nativeHomEndExt`, `OAI.ArExplicit.ExternalTensor.tensorHomEndExt`, `OAI.ArExplicit.T.sourceProductBaseTyped`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ExternalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarEvaluation.lean), [`AuslanderReiten_Ext_ExtKunnethMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethMap.lean), [`AuslanderReiten_Ext_ExternalEvaluatedFreeCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluatedFreeCoordinate.lean), [`AuslanderReiten_Ext_ExternalNativeBarAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalNativeBarAugmentation.lean), [`AuslanderReiten_Ext_ExternalNativeBarInclusion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalNativeBarInclusion.lean), [`AuslanderReiten_Ext_ExternalNativeRegularAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalNativeRegularAugmentation.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean), [`AuslanderReiten_HomComplex_HomCochainNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainNaturality.lean), [`AuslanderReiten_Tensor_TwistedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A123`, `OAIQ031A130`, `OAIQ031A133`, `OAIQ031A134` and `OAIQ031A135` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A148`, `OAIQ031A149` and `OAIQ031A150`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A123
import Definitions.Def_OAIQ031A130
import Definitions.Def_OAIQ031A133
import Definitions.Def_OAIQ031A134
import Definitions.Def_OAIQ031A135

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B
local notation "PM" => ModuleBar.complex k A M
local notation "QN" => ModuleBar.complex k B N

def nativeTotalBarIso : evaluatedTotal k A B X Y P Q ≅ ExternalTensor.complex k A B PM QN :=
  totalEvaluationIso k A B X Y P Q ≪≫
    ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
      (BarBalanced.nativeComplexIso k B N)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

variable (F : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)

def homCochainEndExt (n : ℕ) : Ext X Y n →ₗ[k] Ext X Y n :=
  (homCochainExtEquiv k R P n).toLinearMap.comp
    ((homologyMap F n).hom.comp (homCochainExtEquiv k R P n).symm.toLinearMap)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k : Type u) [Field k]

variable (R : Type u) [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (U : Type u) [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]

def nativeHomEndExt (f : homCochain k R P.complex U ⟶ homCochain k R P.complex U)
    (n : ℕ) : Ext X (ModuleCat.of R U) n →ₗ[k] Ext X (ModuleCat.of R U) n :=
  (homCochainNativeExtEquiv k R P U n).toLinearMap.comp
    ((homologyMap f n).hom.comp (homCochainNativeExtEquiv k R P U n).symm.toLinearMap)

variable (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [Module.Finite k A] [Module.Finite k B]
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (f : homCochain k A P.complex U ⟶ homCochain k A P.complex U)
variable (g : homCochain k B Q.complex V ⟶ homCochain k B Q.complex V)

def tensorHomEndExt (n : ℕ) :
    Ext (moduleObject k A B M N) (moduleObject k A B U V) n →ₗ[k]
      Ext (moduleObject k A B M N) (moduleObject k A B U V) n :=
  nativeHomEndExt k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) (homTensorMap k A B P Q U V f g) n

omit [Module.Finite k A] [Module.Finite k B] in
theorem extKunnethEquiv_apply (n : ℕ)
    (x : Ext (moduleObject k A B M N) (moduleObject k A B U V) n) (p : Diagonal n) :
    extKunnethEquiv k A B P Q U V n x p =
      TensorProduct.map (homCochainExtEquiv k A (Y := U) P p.val.1).toLinearMap
        (homCochainExtEquiv k B (Y := V) Q p.val.2).toLinearMap
        (homKunnethCoordinates k A B P Q U V n
          ((homCochainNativeExtEquiv k (A ⊗[k] B) (projectiveResolution k A B P Q)
            (moduleObject k A B U V) n).symm x) p) := rfl

omit [Module.Finite k A] [Module.Finite k B] in
theorem extKunnethEquiv_tensorHomEndExt (n : ℕ)
    (x : Ext (moduleObject k A B M N) (moduleObject k A B U V) n) (p : Diagonal n) :
    extKunnethEquiv k A B P Q U V n (tensorHomEndExt k A B P Q U V f g n x) p =
      TensorProduct.map (homCochainEndExt k A P f p.val.1)
        (homCochainEndExt k B Q g p.val.2)
        (extKunnethEquiv k A B P Q U V n x p) := by
  rw [extKunnethEquiv_apply, extKunnethEquiv_apply]
  let e := homCochainNativeExtEquiv k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) n
  change TensorProduct.map (homCochainExtEquiv k A (Y := U) P p.val.1).toLinearMap
      (homCochainExtEquiv k B (Y := V) Q p.val.2).toLinearMap
      (homKunnethCoordinates k A B P Q U V n
        (e.symm (e ((homologyMap (homTensorMap k A B P Q U V f g) n).hom (e.symm x)))) p) = _
  erw [LinearEquiv.symm_apply_apply, homKunnethCoordinates_natural]
  exact tensor_conjugate k (homCochainExtEquiv k A (Y := U) P p.val.1)
    (homCochainExtEquiv k B (Y := V) Q p.val.2) (homologyMap f p.val.1).hom
    (homologyMap g p.val.2).hom _

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalNativeBarInclusion
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B
local notation "PM" => ModuleBar.complex k A M
local notation "QN" => ModuleBar.complex k B N

theorem nativeTotalBarIso_f (n : ℕ) :
    (nativeTotalBarIso k A B M N).hom.f n =
      (totalEvaluationTermIso k A B X Y P Q n).hom ≫
        (ExternalTensor.complexMap k A B (BarBalanced.nativeComplexIso k A M).hom
          (BarBalanced.nativeComplexIso k B N).hom).f n := rfl

theorem nativeTotalBarIso_inclusion_zero :
    (productEvaluation k A B X Y).map (ExternalTensor.inclusion k Ae Be P Q 0 0 0 rfl) ≫
      (nativeTotalBarIso k A B M N).hom.f 0 =
    (summandEvaluationIso k A B X Y P Q 0 ⟨(0,0),rfl⟩).hom ≫
      ExternalTensor.mapHom k A B ((BarBalanced.nativeComplexIso k A M).hom.f 0)
        ((BarBalanced.nativeComplexIso k B N).hom.f 0) ≫
      ExternalTensor.inclusion k A B PM QN 0 0 0 rfl := by
  rw [nativeTotalBarIso_f]
  exact inclusion_evaluatedComparison k A B X Y P Q PM QN
    (BarBalanced.nativeComplexIso k A M).hom (BarBalanced.nativeComplexIso k B N).hom
    0 0 0 rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluatedFreeCoordinate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ

def totalFreeEvaluation : (evaluatedTotal k A B X Y P Q).X 0 ⟶
    ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  (nativeTotalBarIso k A B M N).hom.f 0 ≫
    ExternalTensor.barTotalFreeCoordinate k A B M N e f

theorem inclusion_totalFreeEvaluation :
    (productEvaluation k A B X Y).map (ExternalTensor.inclusion k Ae Be P Q 0 0 0 rfl) ≫
      totalFreeEvaluation k A B M N e f =
    (summandEvaluationIso k A B X Y P Q 0 ⟨(0,0),rfl⟩).hom ≫
      ExternalTensor.mapHom k A B ((BarBalanced.nativeComplexIso k A M).hom.f 0)
        ((BarBalanced.nativeComplexIso k B N).hom.f 0) ≫
          ExternalTensor.barFreeCoordinate k A B M N e f :=
  postcompose_square (nativeTotalBarIso_inclusion_zero k A B M N)
    (ExternalTensor.inclusion_barTotalFreeCoordinate k A B M N e f)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalNativeBarAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "XM" => ModuleCat.of A M
local notation "YN" => ModuleCat.of B N
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ

theorem nativeTotalBarIso_augmentation :
    (nativeTotalBarIso k A B M N).hom.f 0 ≫
      (ExternalTensor.augmentation k A B (ModuleBar.nativeResolution k A M)
        (ModuleBar.nativeResolution k B N)).f 0 =
    (productEvaluation k A B XM YN).map
      ((ExternalTensor.augmentation k Ae Be (AbsoluteBar.resolution k A)
        (AbsoluteBar.resolution k B)).f 0) ≫
      totalEndpointMap k A B XM YN (BarBalanced.nativeEndpointIso k A M).hom
        (BarBalanced.nativeEndpointIso k B N).hom :=
  totalEvaluation_augmentation k A B XM YN (AbsoluteBar.resolution k A)
    (AbsoluteBar.resolution k B) (ModuleBar.nativeResolution k A M) (ModuleBar.nativeResolution k B N)
    (BarBalanced.nativeComplexIso k A M) (BarBalanced.nativeComplexIso k B N)
    (BarBalanced.nativeEndpointIso k A M).hom (BarBalanced.nativeEndpointIso k B N).hom
    (BarBalanced.nativeComplexIso_augmentation k A M) (BarBalanced.nativeComplexIso_augmentation k B N)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalRegularEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "UA" => AbsoluteBar.moduleObject k A 0
local notation "UB" => AbsoluteBar.moduleObject k B 0
local notation "XY" => ExternalTensor.moduleObject k A B X Y
local notation "E" => EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B) XY

-- Keep the scalar-ring and evaluation-object presentations used by the endpoint
-- maps. This avoids expanding their tensor-module structures when specializing
-- extensionality to the degree-zero bar objects.
theorem exterior_raw_hom_ext
    (M : ModuleCat.{u} (AbsoluteBar.Enveloping k A)) (N : ModuleCat.{u} (AbsoluteBar.Enveloping k B))
    (Z : ModuleCat.{u} (A ⊗[k] B))
    (f : (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶ Z)
    (g : (E).obj (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N)) ⟶ Z)
    (h : ∀ (a : EnvelopingBimodule k A M) (b : EnvelopingBimodule k B N) (x : X) (y : Y),
      f (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      g (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) : f = g :=
  exterior_hom_ext k A B M N X Y Z f g h

theorem productRegularEndpoint_scalar_pure
    (left : EnvelopingBimodule k A UA) (right : EnvelopingBimodule k B UB) :
    (show A ⊗[k] B from (barTensorZeroEquiv k A B).toModuleIso.hom
      ((bimoduleCoordinates k A B UA UB).symm (left ⊗ₜ[k] right)).value) =
      (show A from left.value) ⊗ₜ[k] (show B from right.value) := by
  rw [bimoduleCoordinates_symm_tmul]
  exact barTensorZeroIso_tmul k A B left.value right.value

theorem productRegularEndpoint_scalar_action (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :
    type_of% ((congrArg (fun scalar : A ⊗[k] B => scalar •
      (ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))
      (productRegularEndpoint_scalar_pure k A B a b)).trans
        (ExternalTensor.smul_tmul k A B X Y a.value b.value x y)) :=
  (congrArg (fun scalar : A ⊗[k] B => scalar •
    (ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))
    (productRegularEndpoint_scalar_pure k A B a b)).trans
      (ExternalTensor.smul_tmul k A B X Y a.value b.value x y)

theorem regularEndpoint_ext :
    type_of% (exterior_raw_hom_ext k A B X Y UA UB XY) :=
  exterior_raw_hom_ext k A B X Y UA UB XY

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalNativeRegularAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local instance instModuleCarrierTensorProductCanonicalTensorObject : Module k (ExternalTensor.canonicalTensorObject k A B M N) :=
  moduleCatBaseModule (k := k) (R := A ⊗[k] B) _
abbrev eval := EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B)
  (ExternalTensor.canonicalTensorObject k A B M N)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

def sourceProductBaseTyped : TwoCone.BaseCokernel (productSourceData q H) 0 ≃ₗ[Te ⊗[k] Te]
    ExternalTensor.moduleObject k Te Te
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0)
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0) :=
  resolutionCokernelEquiv (twistedTensorBarResolution q H)

end ArExplicit.T

end

end OAI
end


