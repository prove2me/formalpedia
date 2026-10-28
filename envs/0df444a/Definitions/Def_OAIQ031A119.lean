-- Prove2me | Definitions.Def_OAIQ031A119
-- name    : OAIQ031A119
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:52:59.278545+00:00
-- url     : https://prove2.me/theorems/fe55d33d-ce7e-4df7-bdd1-7c5a43eead68
-- title:
--   Definitions bundle OAIQ031A119 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 22 definitions and 11 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.fullHomTargetStableLinearEquiv`, `OAI.ArExplicit.CompleteComparison.reversedCokernelMap`, `OAI.ArExplicit.CompleteComparison.targetCocycleMap`, `OAI.ArExplicit.ModuleBar.nativeTensorFirst`, `OAI.ArExplicit.ModuleBar.nativeTensorSecond`, `OAI.ArExplicit.ModuleBar.tensorFirst`, `OAI.ArExplicit.Resolution.dualIdealComparison`, `OAI.ArExplicit.Resolution.idealDualComparison`, `OAI.ArExplicit.Resolution.tConnecting`, `OAI.ArExplicit.Resolution.tDualDerivedIso`, `OAI.ArExplicit.Resolution.tDual_homology_iso`, `OAI.ArExplicit.Resolution.tExplicitP`, `OAI.ArExplicit.Resolution.tExtCoefficientEquiv`, `OAI.ArExplicit.Resolution.tInductionTriangle`, `OAI.ArExplicit.Resolution.tInductionTriangleIso`, `OAI.ArExplicit.Resolution.tTau`, `OAI.ArExplicit.Resolution.tTauMul`, `OAI.ArExplicit.Resolution.tTauMulEquiv`, `OAI.ArExplicit.Resolution.tTauPower`, `OAI.ArExplicit.Resolution.tTriangleA`, `OAI.ArExplicit.Resolution.tTriangleD`, `OAI.ArExplicit.Resolution.tensorIdealComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCubic.lean), [`AuslanderReiten_Bar_ModuleBarNative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNative.lean), [`AuslanderReiten_Bar_ModuleBarTensorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExt.lean), [`AuslanderReiten_Cocycles_ReversedCocycleMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/ReversedCocycleMap.lean), [`AuslanderReiten_Duality_IdealDualComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/IdealDualComparison.lean), [`AuslanderReiten_Ext_TExplicitGenerator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExplicitGenerator.lean), [`AuslanderReiten_Ext_TExtPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtPolynomial.lean), [`AuslanderReiten_Ext_TExtRecurrence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtRecurrence.lean), [`AuslanderReiten_Modules_TInductionHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TInductionHomology.lean), [`AuslanderReiten_Modules_TInductionTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TInductionTriangle.lean), [`AuslanderReiten_Stable_TargetStableCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/TargetStableCoordinates.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A095`, `OAIQ031A105` and `OAIQ031A106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A129`, `OAIQ031A130`, `OAIQ031A131`, `OAIQ031A134` and `OAIQ031A136`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A095
import Definitions.Def_OAIQ031A105
import Definitions.Def_OAIQ031A106

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

include hp in
theorem cubicMap_comm (n : ℕ) :
    cubicMap k R M p (n+1) ≫ (resolution k R M).complex.d (n+1) n =
      (resolution k R M).complex.d (n+4) (n+3) ≫ cubicMap k R M p n := by
  change cubicMap k R M p (n+1) ≫ (complex k R M).d (n+1) n =
    (complex k R M).d (n+3+1) (n+3) ≫ cubicMap k R M p n
  rw [complex_d, complex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact suffixComparison_boundary k R M p hp (n+1) x

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarNative
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]

variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

include hp in
theorem nativeCubicMap_comm (n : ℕ) :
    nativeCubicMap k R M p (n+1) ≫ (nativeResolution k R M).complex.d (n+1) n =
      (nativeResolution k R M).complex.d (n+4) (n+3) ≫ nativeCubicMap k R M p n :=
  cubicMap_comm k R M p hp n

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]

variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

def nativeTensorFirst : Ext (ExternalTensor.canonicalTensorObject k R S M N)
    (ExternalTensor.canonicalTensorObject k R S M N) 3 :=
  ExternalTensor.firstCubicExt k R S (nativeResolution k R M) (nativeResolution k S N)
    (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp)

def nativeTensorSecond : Ext (ExternalTensor.canonicalTensorObject k R S M N)
    (ExternalTensor.canonicalTensorObject k R S M N) 3 :=
  ExternalTensor.secondCubicExt k R S (nativeResolution k R M) (nativeResolution k S N)
    (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr)

def tensorFirst : Ext (ExternalTensor.moduleObject k R S M N)
    (ExternalTensor.moduleObject k R S M N) 3 :=
  (ExternalTensor.selfExtScalarEquiv k R S M N 3).symm (nativeTensorFirst k R S M N p hp)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_ReversedCocycleMap
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

include k

def reversedCokernelMap (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    Cokernel (chainOfCochain K) a →ₗ[R] Cokernel (chainOfCochain L) b :=
  (LinearMap.range ((chainOfCochain K).d (a+1) a).hom).liftQ
    ((LinearMap.range ((chainOfCochain L).d (b+1) b).hom).mkQ.comp
      (reversedComponent x.val a b hab).hom) (by
        rintro _ ⟨y,rfl⟩
        change Submodule.Quotient.mk
          ((reversedComponent x.val a b hab).hom (((chainOfCochain K).d (a+1) a).hom y)) = 0
        have hh := congrArg (fun f => f.hom y) (reversedComponent_comm (k := k) x a b hab)
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨(reversedComponent x.val (a+1) (b+1) (by omega)).hom y, hh⟩)

@[simp] theorem reversedCokernelMap_mk (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b)
    (y : (chainOfCochain K).X a) :
    reversedCokernelMap (k := k) x a b hab (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((reversedComponent x.val a b hab).hom y) := rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualComparison
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def idealDualComparison : DualTensor.dualHomComplex (k := k) (complex q) ≅ idealDualComplex q :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (idealDualEquiv q n).toModuleIso) (by
    intro i j hij
    obtain rfl : i = j + 1 := by simpa using hij.symm
    rw [DualTensor.dualHomComplex_d, idealDualComplex_d]
    apply ModuleCat.hom_ext
    cases j with
    | zero =>
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (fromRightE q (leftU q a)) =
        φ.functional ((fromRightF q a).comp (dU q))
      exact congrArg φ.functional (fromRightF_precompose q a)
    | succ n =>
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      dsimp [idealDualEquiv, idealDualDifferential, DualTensor.dualHomDifferential]
      rw [show (complex q).d (n + 1 + 1) (n + 1) = differential q (n + 1) from ChainComplex.of_d _ _ _]
      change φ.functional (fromRightE q (leftEll q (q ^ n) a)) =
        φ.functional ((fromRightE q a).comp (dEll q (q ^ n)))
      exact congrArg φ.functional (fromRightE_precompose q (q ^ n) a))

def tensorIdealComparison : DualTensor.tensorComplex (k := k) (complex q) ≅ idealDualComplex q :=
  DualTensor.complexIso (complex q) ≪≫ idealDualComparison q

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInductionHomology
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q

def dualIdealComparison :
    TrivialInduction.dualComplex (k := k) (complex q) ≅
      ((TrivialInduction.inflate (k := k)).mapHomologicalComplex _).obj (idealDualComplex q) :=
  TrivialInduction.dualComplexIso (complex q) ≪≫
    ((TrivialInduction.inflate (k := k)).mapHomologicalComplex _).mapIso (tensorIdealComparison q)

theorem tDual_exact (hq : q ≠ 0) (h : NoPositivePowerOne q) (n : ℕ) (hn : n ≠ 2) :
    (TrivialInduction.dualComplex (k := k) (complex q)).ExactAt n := by
  apply (exactAt_iff_of_quasiIsoAt (dualIdealComparison q).hom n).mpr
  exact ModuleRestriction.map_exact _ _ (idealDual_exactAt q hq h n hn)

def tDual_homology_iso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (TrivialInduction.dualComplex (k := k) (complex q)).homology 2 ≅ ModuleCat.of T (Simple q) :=
  HomologicalComplex.homologyMapIso (dualIdealComparison q) 2 ≪≫
    ((idealDualComplex q).sc 2).mapHomologyIso (TrivialInduction.inflate (k := k)) ≪≫
    (TrivialInduction.inflate (k := k)).mapIso (idealDual_homology_two_iso q hq hq1) ≪≫
    inflatedSimpleIso q

def tDualDerivedIso [HasDerivedCategory (ModuleCat T)]
    (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    DerivedCategory.Q.obj
      ((TrivialInduction.dualComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat) ≅
      ((DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q)))⟦(2 : ℤ)⟧ :=
  concentratedNatDerivedIso _ 2 _ (tDual_exact q hq h) (tDual_homology_iso q hq hq1)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInductionTriangle
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q

variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tTriangleA (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    (tSimpleDerived q)⟦(2 : ℤ)⟧ ⟶ tInducedDerived q :=
  (tDualDerivedIso q hq hq1 h).inv ≫ DerivedCategory.Q.map (tExtendedSequence q).f

def tTriangleD (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    tSimpleDerived q ⟶ ((tSimpleDerived q)⟦(2 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
  (tQuotientDerivedIso q h).inv ≫
    DerivedCategory.triangleOfSESδ (tExtendedSequence_shortExact q) ≫
      (tDualDerivedIso q hq hq1 h).hom⟦(1 : ℤ)⟧'

def tInductionTriangle (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :=
  Pretriangulated.Triangle.mk (tTriangleA q hq hq1 h) (tTriangleB q h) (tTriangleD q hq hq1 h)

def tInductionTriangleIso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    DerivedCategory.triangleOfSES (tExtendedSequence_shortExact q) ≅ tInductionTriangle q hq hq1 h :=
  Pretriangulated.Triangle.isoMk _ _ (tDualDerivedIso q hq hq1 h) (Iso.refl _)
    (tQuotientDerivedIso q h)
    (by exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm)
    (by exact (Category.id_comp _).symm)
    (by exact (Iso.hom_inv_id_assoc _ _).symm)

theorem tInductionTriangle_distinguished (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) :
    tInductionTriangle q hq hq1 h ∈ distTriang (DerivedCategory (ModuleCat T)) :=
  Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (tExtendedSequence_shortExact q))
    _ (tInductionTriangleIso q hq hq1 h).symm

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExtRecurrence
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD

def tConnecting (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    ShiftedHom (tSimpleDerived q) (tSimpleDerived q) (3 : ℤ) :=
  tTriangleD q hq hq1 h ≫
    (shiftFunctorAdd' (DerivedCategory (ModuleCat T)) (2 : ℤ) 1 3 (by decide)).inv.app _

theorem tConnecting_multiply_bijective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℤ) (hn : 0 ≤ n) :
    Function.Bijective (fun b : ShiftedHom (tSimpleDerived q) (tSimpleDerived q) n =>
      ShiftedHom.comp (tConnecting q hq hq1 h) b rfl) :=
  TriangleRecurrence.degreeThreeComposition_bijective _ _ _ _ _
    (tInductionTriangle_distinguished q hq hq1 h) n
    (tInducedDerived_hom_zero q hq1 (n + 3) (by omega))
    (tInducedDerived_shift_hom_zero q hq1 (n + 3) (by omega))

def tTau (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) : TSelfExt q 3 :=
  Abelian.Ext.homEquiv.symm (tConnecting q hq hq1 h)

@[simp] theorem tTau_hom (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    (tTau q hq hq1 h).hom = tConnecting q hq hq1 h :=
  Equiv.apply_symm_apply _ _

theorem tTau_multiply_bijective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℕ) :
    Function.Bijective (fun b : TSelfExt q n => (tTau q hq hq1 h).comp b (by omega : 3 + n = n + 3)) := by
  have hb := tConnecting_multiply_bijective q hq hq1 h (n : ℤ) (by omega)
  constructor
  · intro b c hbc
    apply (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
      (Y := ModuleCat.of T (Simple q)) (n := n)).injective
    apply hb.injective
    have hh := congrArg (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
      (Y := ModuleCat.of T (Simple q)) (n := n + 3)) hbc
    simpa only [Abelian.Ext.comp_hom, tTau_hom, Nat.cast_add, Nat.cast_ofNat] using! hh
  · intro z
    let z' : ShiftedHom (tSimpleDerived q) (tSimpleDerived q) ((n : ℤ) + 3) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, tSimpleDerived] using! z.hom
    obtain ⟨b, hbb⟩ := hb.surjective z'
    let b' : TSelfExt q n := Abelian.Ext.homEquiv.symm b
    have hb' : b'.hom = b := Equiv.apply_symm_apply _ _
    refine ⟨b', ?_⟩
    apply (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
      (Y := ModuleCat.of T (Simple q)) (n := n + 3)).injective
    simpa only [Abelian.Ext.comp_hom, tTau_hom, hb', Nat.cast_add, Nat.cast_ofNat] using! hbb

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExtPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

def tTauMul (n : ℕ) : TSelfExt q n →ₗ[k] TSelfExt q (n + 3) :=
  Abelian.Ext.bilinearCompOfLinear k S S S 3 n (n + 3) (by omega) (tTau q hq hq1 h)

def tTauMulEquiv (n : ℕ) : TSelfExt q n ≃ₗ[k] TSelfExt q (n + 3) :=
  LinearEquiv.ofBijective (tTauMul q hq hq1 h n) (tTau_multiply_bijective q hq hq1 h n)

def tExtCoefficientEquiv : (n : ℕ) → k ≃ₗ[k] TSelfExt q (3 * n)
  | 0 => tSimpleExtZeroEquiv q hq1
  | n + 1 => (tExtCoefficientEquiv n).trans (tTauMulEquiv q hq hq1 h (3 * n))

def tTauPower (n : ℕ) : TSelfExt q (3 * n) := tExtCoefficientEquiv q hq hq1 h n 1

@[simp] theorem tTauPower_zero : tTauPower q hq hq1 h 0 = Abelian.Ext.mk₀ (𝟙 S) :=
  tSimpleExtZeroEquiv_one q hq1

@[simp] theorem tTauPower_succ (n : ℕ) :
    tTauPower q hq hq1 h (n + 1) =
      (tTau q hq hq1 h).comp (tTauPower q hq hq1 h n) (by omega) := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExplicitGenerator
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def tExplicitP : TSelfExt q 3 := CocycleData.simpleExtClass q

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_TargetStableCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

def fullHomTargetStableLinearEquiv (b : ℤ) (hb : n = -b)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L n ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) b) :=
  (fullHomStableLinearEquiv K L n hK (hL.cochainShift n)).trans
    (StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L n b hb))

def targetCocycleMap (x : Cocycle K L n) (b : ℤ) (hb : n = -b) :
    Cokernel (chainOfCochain K) 0 →ₗ[R] Cokernel (chainOfCochain L) b :=
  (shiftedCokernelEquiv L n b hb).toLinearMap.comp
    (cokernelMap (cocycleComparisonMap x) 0)

@[simp] theorem fullHomTargetStableLinearEquiv_mk (b : ℤ) (hb : n = -b)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (x : Cocycle K L n) :
    fullHomTargetStableLinearEquiv (k := k) b hb hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (targetCocycleMap x b hb) := by
  change StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L n b hb)
    (fullHomStableEquiv K L n hK (hL.cochainShift n) (CohomologyClass.mk x)) = _
  rw [fullHomStableEquiv_mk, StableHom.targetEquiv_classOf]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end


