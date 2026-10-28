-- Prove2me | Definitions.Def_OAIQ031A121
-- name    : OAIQ031A121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:56:40.097896+00:00
-- url     : https://prove2.me/theorems/2d2fa2d4-4ea4-4ea8-b445-7fef6140bb10
-- title:
--   Definitions bundle OAIQ031A121 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 8 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.canonicalComplexIso`, `OAI.ArExplicit.BarBalanced.canonicalTermTmulProof`, `OAI.ArExplicit.BarBalanced.coefficientPure`, `OAI.ArExplicit.BarBalanced.nativeEndpointIso`, `OAI.ArExplicit.BarBalanced.nativeEndpointObject`, `OAI.ArExplicit.BarBalanced.nativeEvaluatedAugmentation`, `OAI.ArExplicit.ModuleBar.canonicalCoefficientAugmentation`, `OAI.ArExplicit.ModuleBar.canonicalCoefficientTensor`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedCanonical.lean), [`AuslanderReiten_Bar_CanonicalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarEvaluation.lean), [`AuslanderReiten_Bar_CanonicalBarPure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarPure.lean), [`AuslanderReiten_Bar_CanonicalBarSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarSquare.lean), [`AuslanderReiten_Bar_CanonicalBarTermValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarTermValues.lean), [`AuslanderReiten_Bar_NativeBarAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarAugmentation.lean), [`AuslanderReiten_Bar_NativeBarFreeEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarFreeEndpoint.lean), [`AuslanderReiten_Cocycles_SourceCocycleNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/SourceCocycleNaturality.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A098`, `OAIQ031A106` and `OAIQ031A109` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A132`, `OAIQ031A133` and `OAIQ031A134`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A098
import Definitions.Def_OAIQ031A106
import Definitions.Def_OAIQ031A109

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedCanonical
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

/-- Establish compatibility at arbitrary degrees so induction does not unfold the
iterated tensor products in successor degrees. -/
theorem canonicalEquiv_map {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n)
    (g : ModuleBar.moduleObject k R X m →ₗ[R] ModuleBar.moduleObject k R X n)
    (h : ∀ (a : AbsoluteBar.moduleObject k R m) (x : X),
      rawEval k R X n (f a ⊗ₜ[k] x) = g (rawEval k R X m (a ⊗ₜ[k] x)))
    (z : canonicalEvaluated k R X m) :
    canonicalEquiv k R X n (canonicalMap k R X f z) =
      g (canonicalEquiv k R X m z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a x =>
    rw [canonicalMap_tmul, canonicalEquiv_tmul, canonicalEquiv_tmul]
    exact h a.value x

theorem canonicalEquiv_differential (n : ℕ) (z : canonicalEvaluated k R X (n+1)) :
    canonicalEquiv k R X n
      (canonicalMap k R X (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
        (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n)) z) =
    ModuleBar.differential k R X n (canonicalEquiv k R X (n+1) z) := by
  exact canonicalEquiv_map k R X (m := n+1) (n := n)
    (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
      (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n))
    (ModuleBar.differential k R X n) (rawEval_boundary k R X n) z

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarSquare
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem canonical_square {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n)
    (g : ModuleBar.moduleObject k R X m ⟶ ModuleBar.moduleObject k R X n)
    (h : ∀ z, canonicalEquiv k R X n (canonicalMap k R X f z) =
      g (canonicalEquiv k R X m z)) :
    (EnvelopingBimodule.evaluationFunctor k R X).map f ≫
        (canonicalEquiv k R X n).toModuleIso.hom =
      (canonicalEquiv k R X m).toModuleIso.hom ≫ g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact h z

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

omit [CharP k 2] in
theorem canonicalDifferentialSquare (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k R X).map
      (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
        (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n)) ≫
      (canonicalEquiv k R X n).toModuleIso.hom =
    (canonicalEquiv k R X (n+1)).toModuleIso.hom ≫
      ModuleCat.ofHom (X := ModuleBar.moduleObject k R X (n+1))
        (Y := ModuleBar.moduleObject k R X n) (ModuleBar.differential k R X n) :=
  canonical_square k R X (m := n+1) (n := n)
    (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
      (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n))
    (ModuleCat.ofHom (X := ModuleBar.moduleObject k R X (n+1))
      (Y := ModuleBar.moduleObject k R X n) (ModuleBar.differential k R X n))
    (canonicalEquiv_differential k R X n)

theorem canonicalTermIso_d (n : ℕ) :
    (canonicalTermIso k R X (n+1)).hom ≫ (ModuleBar.complex k R X).d (n+1) n =
      (ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R)).d (n+1) n ≫
        (canonicalTermIso k R X n).hom := by
  change _ ≫ (ModuleBar.complex k R X).d (n+1) n =
    (EnvelopingBimodule.evaluationFunctor k R X).map
      ((AbsoluteBar.complex k R).d (n+1) n) ≫ _
  rw [ModuleBar.complex_d, AbsoluteBar.complex_d]
  exact (canonicalDifferentialSquare k R X (n+1)).symm

def canonicalComplexIso :
    ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R) ≅ ModuleBar.complex k R X :=
  HomologicalComplex.Hom.isoOfComponents (canonicalTermIso k R X)
    (fun i j hij => by
      have h : j+1=i := hij
      subst i
      exact canonicalTermIso_d k R X j)

theorem canonicalComplexIso_f (n : ℕ) :
    (canonicalComplexIso k R X).hom.f n = (canonicalTermIso k R X n).hom := rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarTermValues
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [charP : CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

abbrev canonicalTermTmulProof (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R (n+1))) (x : X) :=
  canonicalEquiv_tmul k R X (n+1) z x

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarPure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def coefficientPure (a : R) (x : X) : (ModuleBar.complex k R X).X 0 :=
  a ⊗ₜ[k] x

omit [CharP k 2] in
theorem rawEval_pure (a b : R) (x : X) :
    rawEval k R X 1 ((a ⊗ₜ[k] b) ⊗ₜ[k] x) = a ⊗ₜ[k] (b • x) := by
  rw [rawEval_succ, rawEval_zero]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarAugmentation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

def canonicalCoefficientAugmentation :
    (canonicalCoefficientComplex k R M).X 0 ⟶ ModuleCat.of R M := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (nativeResolution k R M).π.f 0

end ArExplicit.ModuleBar

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def nativeEndpointObject : ModuleCat.{u} R := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (EnvelopingBimodule.evaluationFunctor k R (ModuleCat.of R M)).obj
    (AbsoluteBar.moduleObject k R 0)

def nativeEndpointIso :
    nativeEndpointObject k R M ≅ ModuleCat.of R M := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (canonicalEquiv k R (ModuleCat.of R M) 0).toModuleIso

def nativeEvaluatedAugmentation :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X 0 ⟶
      nativeEndpointObject k R M := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (EnvelopingBimodule.evaluationFunctor k R (ModuleCat.of R M)).map
    ((AbsoluteBar.resolution k R).π.f 0)

omit [Module k M] [IsScalarTower k R M] in
theorem canonicalComplexIso_augmentation :
    nativeEvaluatedAugmentation k R M ≫ (nativeEndpointIso k R M).hom =
      (canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        ModuleBar.canonicalCoefficientAugmentation k R M := by
  let : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact canonicalDifferentialSquare k R (ModuleCat.of R M) 0

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarFreeEndpoint
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

def canonicalCoefficientTensor (a : R) (m : M) : (canonicalCoefficientComplex k R M).X 0 :=
  BarBalanced.coefficientPure k R (ModuleCat.of R M) a m

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SourceCocycleNaturality
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

include k in
theorem sourceCocycleMap_precomp (f : K ⟶ L) (x : Cocycle L M n) :
    sourceCocycleMap (x.precomp f) =
      (sourceCocycleMap x).comp (cokernelMap (extendMap f negIndexEmbedding) n) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((chainOfCochain K).d (n+1) n).hom) z
  change sourceCocycleMap (x.precomp f) (Submodule.Quotient.mk z) =
    sourceCocycleMap x (Submodule.Quotient.mk (((extendMap f negIndexEmbedding).f n).hom z))
  rw [sourceCocycleMap_mk (k := k), sourceCocycleMap_mk (k := k), sourceCocycleComponent_precomp]
  rfl

include k in
theorem sourceCocycleMap_postcomp (x : Cocycle K L n) (f : L ⟶ M) :
    sourceCocycleMap (x.postcomp f) =
      (cokernelMap (extendMap f negIndexEmbedding) 0).comp (sourceCocycleMap x) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((chainOfCochain K).d (n+1) n).hom) z
  change sourceCocycleMap (x.postcomp f) (Submodule.Quotient.mk z) =
    cokernelMap (extendMap f negIndexEmbedding) 0 (sourceCocycleMap x (Submodule.Quotient.mk z))
  rw [sourceCocycleMap_mk (k := k), sourceCocycleMap_mk (k := k), sourceCocycleComponent_postcomp]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end


