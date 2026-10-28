-- Prove2me | Definitions.Def_OAIQ031A148
-- name    : OAIQ031A148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:25:05.844519+00:00
-- url     : https://prove2.me/theorems/cd412478-6948-49de-a1db-98201bce5ff5
-- title:
--   Definitions bundle OAIQ031A148 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 5 definitions and 23 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.barPureTensor`, `OAI.ArExplicit.ExternalBalanced.nativePureStart`, `OAI.ArExplicit.ExternalBalanced.summandFreeProof`, `OAI.ArExplicit.FiniteLeftModule.moduleExtSourceStableEquiv`, `OAI.ArExplicit.FiniteLeftModule.resolutionSourceAtStableEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_CanonicalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarEvaluation.lean), [`AuslanderReiten_Bar_ExternalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarEvaluation.lean), [`AuslanderReiten_Bar_NativeBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarEvaluation.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_FiniteConnectingProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteConnectingProducts.lean), [`AuslanderReiten_Coordinates_FiniteExtSourceCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteExtSourceCoordinates.lean), [`AuslanderReiten_Evaluation_CanonicalRegularMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/CanonicalRegularMap.lean), [`AuslanderReiten_Ext_ExternalEvaluatedFreeValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluatedFreeValues.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A141`, `OAIQ031A142` and `OAIQ031A143` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A151`, `OAIQ031A152` and `OAIQ031A153`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A141
import Definitions.Def_OAIQ031A142
import Definitions.Def_OAIQ031A143

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

theorem canonicalComplexIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k R X).map
      (cubicHom k R p n) ≫
      (canonicalComplexIso k R X).hom.f n =
    (canonicalComplexIso k R X).hom.f (n+3) ≫ ModuleBar.cubicMap k R X p n := by
  rw [canonicalComplexIso_f, canonicalComplexIso_f]
  exact canonicalTermIso_cubic k R X p n

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

omit [Module k M] [IsScalarTower k R M] in
theorem nativeEvaluatedCubic_canonical (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    nativeEvaluatedCubic k R M p n ≫
      (canonicalComplexIso k R (ModuleCat.of R M)).hom.f n =
    (canonicalComplexIso k R (ModuleCat.of R M)).hom.f (n+3) ≫
      ModuleBar.canonicalCoefficientCubic k R M p n :=
  canonicalComplexIso_cubic k R (ModuleCat.of R M) p n

theorem nativeComplexIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    nativeEvaluatedCubic k R M p n ≫
      (nativeComplexIso k R M).hom.f n =
    (nativeComplexIso k R M).hom.f (n+3) ≫ ModuleBar.cubicMap k R M p n :=
  comparisonIso_trans (canonicalComplexIso k R (ModuleCat.of R M))
    (ModuleBar.coefficientScalarIso k R M) (n+3) n
    (nativeEvaluatedCubic k R M p n) (ModuleBar.canonicalCoefficientCubic k R M p n)
    (ModuleBar.cubicMap k R M p n) (nativeEvaluatedCubic_canonical k R M p n)
    (ModuleBar.coefficientScalarIso_cubic k R M p n)

end ArExplicit.BarBalanced

end

end OAI
end

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
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q
local notation "PM" => ModuleBar.complex k A M
local notation "QN" => ModuleBar.complex k B N

theorem firstCubic_nativeFactors (p : AbsoluteBar.Cochain3 k A) (n : ℕ) :
    ModuleCat.ofHom (ExternalTensor.firstCubic k A B PE QE
      (evaluatedFirstComparison k A X P (barCubic k A p)) n) ≫
      (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f n =
    (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k A B PM QN (ModuleBar.cubicMap k A M p) n) := by
  apply ExternalTensor.firstCubic_complexMap k A B
  intro j
  exact BarBalanced.nativeComplexIso_cubic k A M p j

theorem secondCubic_nativeFactors (p : AbsoluteBar.Cochain3 k B) (n : ℕ) :
    ModuleCat.ofHom (ExternalTensor.secondCubic k A B PE QE
      (evaluatedSecondComparison k B Y Q (barCubic k B p)) n) ≫
      (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f n =
    (ExternalTensor.complexIso k A B (BarBalanced.nativeComplexIso k A M)
        (BarBalanced.nativeComplexIso k B N)).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k A B PM QN (ModuleBar.cubicMap k B N p) n) := by
  apply ExternalTensor.secondCubic_complexMap k A B
  intro j
  exact BarBalanced.nativeComplexIso_cubic k B N p j

theorem nativeTotalBarIso_first (p : AbsoluteBar.Cochain3 k A) (n : ℕ) :
    (productEvaluation k A B X Y).map
      (ModuleCat.ofHom (ExternalTensor.firstCubic k Ae Be P Q (barCubic k A p) n)) ≫
      (nativeTotalBarIso k A B M N).hom.f n =
    (nativeTotalBarIso k A B M N).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k A B PM QN (ModuleBar.cubicMap k A M p) n) := by
  exact compose_squares
    (firstCubic_totalEvaluation k A B X Y P Q (barCubic k A p) n)
    (firstCubic_nativeFactors k A B M N p n)

theorem nativeTotalBarIso_second (p : AbsoluteBar.Cochain3 k B) (n : ℕ) :
    (productEvaluation k A B X Y).map
      (ModuleCat.ofHom (ExternalTensor.secondCubic k Ae Be P Q (barCubic k B p) n)) ≫
      (nativeTotalBarIso k A B M N).hom.f n =
    (nativeTotalBarIso k A B M N).hom.f (n+3) ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k A B PM QN (ModuleBar.cubicMap k B N p) n) := by
  exact compose_squares
    (secondCubic_totalEvaluation k A B X Y P Q (barCubic k B p) n)
    (secondCubic_nativeFactors k A B M N p n)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

@[simp]
theorem topCokernelProjection_mk (n : ℕ) (a : D.term n) (b c : D.term (n + 2))
    (e : D.term (n + 4)) :
    topCokernelProjection D n (Submodule.Quotient.mk ((a, b), (c, e))) =
      Submodule.Quotient.mk e := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteConnectingProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]
variable (τ : FrobeniusTrace k R)

def resolutionSourceAtStableEquiv (S M : FiniteLeftModule k R) (n : ℤ) :
    CohomologyClass (S.completeCochain τ) (M.completeCochain τ) n ≃+
      StableHom R (RawCokernelAt (S.completeCochain τ) n) M.carrier :=
  (rawSourceAtStableEquiv (k := k) _ _ n
    (S.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      (StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ)).targetAddEquiv

omit [CharP k 2] in
@[simp]
theorem resolutionSourceAtStableEquiv_mk (S M : FiniteLeftModule k R) (n : ℤ)
    (x : Cocycle (S.completeCochain τ) (M.completeCochain τ) n) :
    resolutionSourceAtStableEquiv τ S M n (CohomologyClass.mk x) =
      StableHom.classOf R _ _ ((M.completeCochainCokernelEquiv τ).toLinearMap.comp (rawSourceAt x)) := by
  simp only [resolutionSourceAtStableEquiv, AddEquiv.trans_apply, rawSourceAtStableEquiv_mk,
    StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteExtSourceCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

def moduleExtSourceStableEquiv (N : ModuleCat.{u} R) (n : ℕ) :
    Ext M.carrier N (n+1) ≃+
      StableHom R (RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ)) N :=
  (extSourceIso (k := k) (M.fullCokernelEquiv τ).toModuleIso.symm N (n+1)).toAddEquiv.trans
    ((positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain N n).toAddEquiv.trans
      (StableIsomorphism.ofLinearEquiv
        (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv)

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_CanonicalRegularMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R) (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable (f : M ⟶ AbsoluteBar.moduleObject k R 0)

theorem regularMap_tmul (m : EnvelopingBimodule k R M) (x : X) :
    regularMap k R X M f (BalancedTensor.tmul m x) =
      (show R from f m.value) • x := by
  change (nativeEndpointIso k R X).hom
    (BalancedTensor.tmul (EnvelopingBimodule.map f m) x) = _
  rw [nativeEndpointIso_tmul_value]
  rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluatedFreeValues
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
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B

-- Match the native chain maps' complex shape and scalar structures in the premises.
-- Keep the summand presentation in the conclusion so composition does not need to
-- compare expanded tensor-product structures after specializing the bar complexes.
theorem postShuffle_native_values
    (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
    (g : (factorEvaluation k U (AbsoluteBar.complex k A)).X 0 ⟶
      (ModuleBar.complex k A M).X (c := ComplexShape.down ℕ) 0)
    (h : (factorEvaluation k V (AbsoluteBar.complex k B)).X 0 ⟶
      (ModuleBar.complex k B N).X (c := ComplexShape.down ℕ) 0)
    (a : EnvelopingBimodule k A (AbsoluteBar.moduleObject k A (0+1)))
    (b : EnvelopingBimodule k B (AbsoluteBar.moduleObject k B (0+1)))
    (x : U) (y : V) (r : A) (s : B)
    (hg : (g ≫ (ModuleBar.freeCoordinate k A M e).toModuleIso.hom)
      (@BalancedTensor.tmul k A (EnvelopingBimodule k A (AbsoluteBar.moduleObject k A (0+1))) U _ _ _ _
        (@EnvelopingBimodule.instModule_1 k A _ _ _ (AbsoluteBar.moduleObject k A (0+1))
          (moduleCatBaseModule k (A ⊗[k] Aᵐᵒᵖ) (AbsoluteBar.moduleObject k A (0+1))))
        (moduleCatBaseModule k A U) _ _ a x) = r)
    (hh : (h ≫ (ModuleBar.freeCoordinate k B N f).toModuleIso.hom)
      (@BalancedTensor.tmul k B (EnvelopingBimodule k B (AbsoluteBar.moduleObject k B (0+1))) V _ _ _ _
        (@EnvelopingBimodule.instModule_1 k B _ _ _ (AbsoluteBar.moduleObject k B (0+1))
          (moduleCatBaseModule k (B ⊗[k] Bᵐᵒᵖ) (AbsoluteBar.moduleObject k B (0+1))))
        (moduleCatBaseModule k B V) _ _ b y) = s) :
    ((summandEvaluationIso k A B U V (AbsoluteBar.complex k A) (AbsoluteBar.complex k B) 0 ⟨(0,0),rfl⟩).hom ≫
      ExternalTensor.mapHom k A B
        (show (factorEvaluation k U (AbsoluteBar.complex k A)).X 0 ⟶ (ModuleBar.complex k A M).X 0 from g)
        (show (factorEvaluation k V (AbsoluteBar.complex k B)).X 0 ⟶ (ModuleBar.complex k B N).X 0 from h) ≫
      ExternalTensor.barFreeCoordinate k A B M N e f)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B ((AbsoluteBar.complex k A).X 0) ((AbsoluteBar.complex k B).X 0)).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B U V).symm (x ⊗ₜ[k] y))) = r ⊗ₜ[k] s :=
  postShuffle_barFree_values k A B M N e f
    ((AbsoluteBar.complex k A).X 0) ((AbsoluteBar.complex k B).X 0) U V g h a b x y r s hg hh

theorem nativePostShuffle :
    type_of% (postShuffle_native_values k A B M N e f X Y
      ((BarBalanced.nativeComplexIso k A M).hom.f 0)
      ((BarBalanced.nativeComplexIso k B N).hom.f 0)) :=
  postShuffle_native_values k A B M N e f X Y
    ((BarBalanced.nativeComplexIso k A M).hom.f 0)
    ((BarBalanced.nativeComplexIso k B N).hom.f 0)

abbrev nativePureStart (a b : A) (c d : B) (m : M) (n : N) :=
  nativePostShuffle k A B M N e f
    (⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k A (AbsoluteBar.moduleObject k A 1))
    (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k B (AbsoluteBar.moduleObject k B 1)) m n
    (e (b • m) • a) (f (d • n) • c)

theorem nativePureLeft (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (nativePureStart k A B M N e f a b c d m n
      (BarBalanced.nativeComposite_tensor k A M e a b m)) :=
  nativePureStart k A B M N e f a b c d m n
    (BarBalanced.nativeComposite_tensor k A M e a b m)

theorem nativePureProof (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (nativePureLeft k A B M N e f a b c d m n
      (BarBalanced.nativeComposite_tensor k B N f c d n)) :=
  nativePureLeft k A B M N e f a b c d m n
    (BarBalanced.nativeComposite_tensor k B N f c d n)

theorem shuffledFreeEvaluation_pure (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (nativePureProof k A B M N e f a b c d m n) :=
  nativePureProof k A B M N e f a b c d m n

abbrev summandFreeProof (a b : A) (c d : B) (m : M) (n : N) :=
  shuffledFreeEvaluation_pure k A B M N e f a b c d m n

theorem summandFreeEvaluation_pure (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (summandFreeProof k A B M N e f a b c d m n) :=
  summandFreeProof k A B M N e f a b c d m n

theorem totalFreeFromSummand :
    type_of% (valueOfComposite (inclusion_totalFreeEvaluation k A B M N e f)) :=
  valueOfComposite (inclusion_totalFreeEvaluation k A B M N e f)

abbrev barPureTensor (a b : A) (c d : B) (m : M) (n : N) :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := A) X
  letI : Module k N := moduleCatBaseModule (k := k) (R := B) Y
  BalancedTensor.tmul (k := k) (R := A ⊗[k] B)
    ((bimoduleCoordinates k A B ((P).X 0) ((Q).X 0)).symm
      ((⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k A (AbsoluteBar.moduleObject k A 1)) ⊗ₜ[k]
        (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k B (AbsoluteBar.moduleObject k B 1))))
    ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (m ⊗ₜ[k] n))

theorem totalFreeAt (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (totalFreeFromSummand k A B M N e f
      (barPureTensor k A B M N a b c d m n)) :=
  totalFreeFromSummand k A B M N e f (barPureTensor k A B M N a b c d m n)

theorem totalFreeProof (a b : A) (c d : B) (m : M) (n : N) :
    type_of% ((totalFreeAt k A B M N e f a b c d m n).trans
      (summandFreeEvaluation_pure k A B M N e f a b c d m n)) :=
  (totalFreeAt k A B M N e f a b c d m n).trans
    (summandFreeEvaluation_pure k A B M N e f a b c d m n)

theorem totalFreeEvaluation_pure (a b : A) (c d : B) (m : M) (n : N) :
    type_of% (totalFreeProof k A B M N e f a b c d m n) :=
  totalFreeProof k A B M N e f a b c d m n

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
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)


theorem regularMap_tmul_of_smul
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) (f : M ⟶ AbsoluteBar.moduleObject k R 0)
    (m : EnvelopingBimodule k R M) (x y : X)
    (h : (show R from f m.value) • x = y) :
    regularMap k R X M f (BalancedTensor.tmul m x) = y :=
  (regularMap_tmul k R X M f m x).trans h

theorem namedRegularMap_tmul_of_smul
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) (f : M ⟶ AbsoluteBar.moduleObject k R 0)
    (g : (EnvelopingBimodule.evaluationFunctor k R X).obj M ⟶ X)
    (hg : g = regularMap k R X M f)
    (m : EnvelopingBimodule k R M) (x y : X)
    (h : (show R from f m.value) • x = y) :
    g (BalancedTensor.tmul m x) = y :=
  (congrArg (fun q : (EnvelopingBimodule.evaluationFunctor k R X).obj M ⟶ X =>
    q (BalancedTensor.tmul m x)) hg).trans
      (regularMap_tmul_of_smul k R X M f m x y h)

end ArExplicit.BarBalanced

namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "UA" => AbsoluteBar.moduleObject k A 0
local notation "UB" => AbsoluteBar.moduleObject k B 0

theorem factorRegularEndpoint_pure (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :
    factorRegularEndpoint k A B X Y (BalancedTensor.tmul
      ((bimoduleCoordinates k A B UA UB).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      ((show A from a.value) • x) ⊗ₜ[k] ((show B from b.value) • y) := by
  change ExternalTensor.map k A B (BarBalanced.nativeEndpointIso k A X).hom.hom
    (BarBalanced.nativeEndpointIso k B Y).hom.hom
    (shuffle k A B UA UB X Y (BalancedTensor.tmul
      ((bimoduleCoordinates k A B UA UB).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) = _
  erw [shuffle_pure, ExternalTensor.map_tmul]
  erw [BarBalanced.nativeEndpointIso_tmul k A X a x, BarBalanced.nativeEndpointIso_tmul k B Y b y]

end ArExplicit.ExternalBalanced

end

end OAI
end


