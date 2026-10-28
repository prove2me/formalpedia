-- Prove2me | Definitions.Def_OAIQ031A141
-- name    : OAIQ031A141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:20:45.613798+00:00
-- url     : https://prove2.me/theorems/4d3d06af-d6f6-4063-851f-05a77447c380
-- title:
--   Definitions bundle OAIQ031A141 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 4 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.factorRegularEndpoint`, `OAI.ArExplicit.FullTate.model`, `OAI.ArExplicit.ModuleBar.nativeTensorKunneth`, `OAI.ArExplicit.ModuleBar.tensorKunneth`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_CanonicalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarEvaluation.lean), [`AuslanderReiten_Bar_ModuleBarTensorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExt.lean), [`AuslanderReiten_Bar_ModuleBarTensorProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorProducts.lean), [`AuslanderReiten_Complete_CompleteTailExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailExt.lean), [`AuslanderReiten_Complete_FullTateModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FullTateModel.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean), [`AuslanderReiten_Tensor_BalancedTensorCanonicalEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCanonicalEndpoint.lean), [`AuslanderReiten_Tensor_BalancedTensorCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCompleteAction.lean), [`AuslanderReiten_Tensor_BalancedTensorCompleteInverse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCompleteInverse.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A130`, `OAIQ031A131`, `OAIQ031A132`, `OAIQ031A133` and `OAIQ031A134` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A146`, `OAIQ031A147` and `OAIQ031A148`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A130
import Definitions.Def_OAIQ031A131
import Definitions.Def_OAIQ031A132
import Definitions.Def_OAIQ031A133
import Definitions.Def_OAIQ031A134

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

theorem canonicalTermIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k R X).map
      (cubicHom k R p n) ≫
      (canonicalTermIso k R X n).hom =
    (canonicalTermIso k R X (n+3)).hom ≫ ModuleBar.cubicMap k R X p n := by
  exact canonical_square k R X (m := n+4) (n := n+1)
    (cubicHom k R p n) (ModuleBar.cubicMap k R X p n)
    (canonicalEquiv_cubic k R X p n)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]

def nativeTensorKunneth (n : ℕ) :
    Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n ≃ₗ[k]
        ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
          (ModuleCat.of S N) (ModuleCat.of S N) n :=
  ExternalTensor.extKunnethEquiv k R S (nativeResolution k R M) (nativeResolution k S N)
    (ModuleCat.of R M) (ModuleCat.of S N) n

def tensorKunneth (n : ℕ) :
    Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n ≃ₗ[k]
      ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) n :=
  (ExternalTensor.selfExtScalarEquiv k R S M N n).trans (nativeTensorKunneth k R S M N n)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

theorem tensorCubics_commute :
    (tensorFirst k R S M N p hp).comp (tensorSecond k R S M N r hr) rfl =
      (tensorSecond k R S M N r hr).comp (tensorFirst k R S M N p hp) rfl := by
  unfold tensorFirst tensorSecond
  rw [← ExternalTensor.selfExtScalarEquiv_symm_comp,
    ← ExternalTensor.selfExtScalarEquiv_symm_comp]
  exact congrArg (ExternalTensor.selfExtScalarEquiv k R S M N 6).symm
    (nativeTensorCubics_commute k R S M N p hp r hr)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S)

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesProjectiveObjects]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (R := R) (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (R := S) (chainOfCochain (functorComplex F K)))
variable (e : ModuleCat.of S (Cokernel (chainOfCochain (functorComplex F K)) 0) ≅
  F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
variable (hπ : (tailFunctorHom F K).f 0 ≫ F.map (((completeExtResolution (R := R) hK)).π.f 0) = ((completeExtResolution (R := S) hFK)).π.f 0 ≫ e.hom)
include hπ

theorem restrictedEndExt_functor (r : ℕ) (x : Cocycle K K (r : ℤ)) :
    restrictedEndExt (k := k) (functorComplex F K) hFK r
      (fullHomCocycleMap F K K (r : ℤ) x) =
    ((Ext.mk₀ e.hom).comp
      ((restrictedEndExt (k := k) K hK r x).mapExactFunctor F) (zero_add r)).comp
        (Ext.mk₀ e.inv) (add_zero r) := by
  exact ResolutionProducts.natComparisonEndExt_map (k := k) F
    (completeExtResolution hK) (completeExtResolution hFK) e
    (completeTailResolutionHom F K hK hFK e hπ) r
    (cochainTailMap K K r x.val) (cochainTailMap_comm (k := k) K K r x)
    (cochainTailMap (functorComplex F K) (functorComplex F K) r
      (fullHomCocycleMap F K K (r : ℤ) x).val)
    (cochainTailMap_comm (k := k) _ _ r (fullHomCocycleMap F K K (r : ℤ) x))
    (tailFunctor_augmentation F K hK hFK e hπ r x.val)

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_FullTateModel
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FullTate
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
open CompleteComparison TateKoszul
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b)=τ.trace (b*a))
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

variable {K}

def model {p q : CohomologyClass K K 3} (P : PositiveModel (k := k) K p q) :
    TateKoszul.Model (fun a => fullHomRightMultiply (k := k) (K := K) (L := K) (M := K) (n := a) p)
      (fun a => fullHomRightMultiply (k := k) (K := K) (L := K) (M := K) (n := a) q) where
  positive := P.positive
  negative := negativeChart τ hs hK P.positive
  outside a hp hn := by
    by_cases ha : 0 ≤ a
    · exact P.outside a ha hp
    · have hb : 0 ≤ -a-1 := by omega
      have hnb : ∀ n : ℕ, -a-1 ≠ 3*(n:ℤ) := by
        intro n h
        exact hn n (by omega)
      let := P.outside (-a-1) hb hnb
      let e := τ.fullHomSourceDualityAt hs K hK (-a-1) a (by omega)
      exact ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩
  positive_x := P.right_x
  positive_y := P.right_y
  negative_x := negativeChart_action τ hs hK P.positive p (BinaryKoszul.mulX k) P.left_x
  negative_y := negativeChart_action τ hs hK P.positive q (BinaryKoszul.mulY k) P.left_y

end ArExplicit.FullTate

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalRegularEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def factorRegularEndpoint :
    (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB) ⟶ XY :=
  totalEndpointMap k A B X Y (BarBalanced.nativeEndpointIso k A X).hom
    (BarBalanced.nativeEndpointIso k B Y).hom

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCanonicalEndpoint
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.BalancedTensor
open CompleteComparison
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := S) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := S) (F := F))]
variable [(functor (k := k) (R := R) (S := S) (F := F)).PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain
  (functorComplex (functor (k := k) (R := R) (S := S) (F := F)) K)))

theorem rawFunctorEndpointIso_eq :
    rawFunctorEndpointIso (functor (k := k) (R := R) (S := S) (F := F)) K hK hFK =
      (cochainCokernelEquiv (k := k) (F := F) (S := S) K).toModuleIso := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((functorComplex (functor (k := k) (R := R) (S := S) (F := F)) K).d (-1) 0).hom) z
  have h := congrArg (fun f => f.hom x)
    (rawFunctorEndpointIso_augmentation (functor (k := k) (R := R) (S := S) (F := F)) K hK hFK)
  exact h.symm.trans (cokernelEquiv_mk (k := k) (F := F) (S := S) (K.d (-1) 0).hom x).symm

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCompleteAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
open CompleteComparison
universe u
variable {k R F : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
variable [HasDerivedCategory (ModuleCat.{u} R)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [(functor (k := k) (R := R) (S := R) (F := F)).PreservesProjectiveObjects]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeActionCokernelIso_eq : completeActionCokernelIso τ M e =
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans
      (M.completeCochainCokernelEquiv τ).symm).toModuleIso := by
  rw [completeActionCokernelIso, rawFunctorEndpointIso_eq]
  apply Iso.ext
  have ht := congrArg (fun f =>
    (cochainCokernelEquiv (k := k) (F := F) (S := R) (M.completeCochain τ)).toModuleIso.hom ≫
      f ≫ e.toModuleIso.hom ≫ (M.completeCochainCokernelEquiv τ).toModuleIso.inv)
    (nativeObjectIso_natural (k := k) (F := F) (S := R)
      (M.completeCochainCokernelEquiv τ).toLinearMap)
  exact ht

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeActionOut_quotient :
    (HomotopyCategory.quotient _ _).map (completeActionOut τ M e) =
      (completeTensorIso τ M M e).hom := by
  unfold completeActionOut
  rw [completeActionCokernelIso_eq]
  exact cokernelCochainLift_quotient _ _ _

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCompleteInverse
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [(functor (k := k) (R := R) (S := R) (F := F)).PreservesProjectiveObjects]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

theorem completeActionIn_quotient :
    (HomotopyCategory.quotient _ _).map (completeActionIn τ M e) =
      (completeTensorIso τ M M e).inv := by
  apply (cancel_mono (completeTensorIso τ M M e).hom).1
  have h := completeAction_inverse τ M e
  rw [CategoryTheory.Functor.map_comp, completeActionOut_quotient] at h
  exact h.trans (completeTensorIso τ M M e).inv_hom_id.symm

end ArExplicit.BalancedTensor

end

end OAI
end


