-- Prove2me | Definitions.Def_OAIQ031A122
-- name    : OAIQ031A122
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:05:50.690234+00:00
-- url     : https://prove2.me/theorems/ec87aeca-e407-48f6-9b6a-c2b47d87e766
-- title:
--   Definitions bundle OAIQ031A122 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 8 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.nativeEvaluatedCubic`, `OAI.ArExplicit.CompleteComparison.rawCokernelAtEquiv`, `OAI.ArExplicit.CompleteComparison.rawCokernelAtInclusion`, `OAI.ArExplicit.CompleteComparison.rawSourceAt`, `OAI.ArExplicit.CompleteComparison.rawSourceAtStableEquiv`, `OAI.ArExplicit.CompleteComparison.rawSourceStableEquiv`, `OAI.ArExplicit.ModuleBar.canonicalCoefficientCubic`, `OAI.ArExplicit.ModuleBar.nativeTensorHomTransport`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarScalarTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarScalarTransport.lean), [`AuslanderReiten_Bar_ModuleBarTensorHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorHom.lean), [`AuslanderReiten_Bar_NativeBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarEvaluation.lean), [`AuslanderReiten_Stable_RawSourceCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/RawSourceCoordinates.lean), [`AuslanderReiten_Stable_RawSourceDegrees`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/RawSourceDegrees.lean), [`AuslanderReiten_Stable_RawSourceStable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/RawSourceStable.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A106`, `OAIQ031A109`, `OAIQ031A110`, `OAIQ031A111` and `OAIQ031A114` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A134` and `OAIQ031A135`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A106
import Definitions.Def_OAIQ031A109
import Definitions.Def_OAIQ031A110
import Definitions.Def_OAIQ031A111
import Definitions.Def_OAIQ031A114

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarScalarTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def canonicalCoefficientCubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (canonicalCoefficientComplex k R M).X (n+3) ⟶ (canonicalCoefficientComplex k R M).X n := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact cubicMap k R M p n

theorem coefficientScalarIso_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    canonicalCoefficientCubic k R M p n ≫ (coefficientScalarIso k R M).hom.f n =
      (coefficientScalarIso k R M).hom.f (n+3) ≫ cubicMap k R M p n := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev nativeTensorHomTransport :=
  ExternalTensor.homTensorMap k R S (nativeResolution k R M) (nativeResolution k S N)
    (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def nativeEvaluatedCubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X (n+3) ⟶
      (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X n := by
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  exact (EnvelopingBimodule.evaluationFunctor k R (ModuleCat.of R M)).map
    (ModuleCat.ofHom (X := (AbsoluteBar.complex k R).X (n+3))
      (Y := (AbsoluteBar.complex k R).X n) (AbsoluteBar.suffixComparisonMap k R p n))

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_RawSourceCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

variable {k : Type u} [Field k] [CharP k 2] [Algebra k R]
variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

include k in
@[simp]
theorem rawSourceCocycleMap_mk (x : Cocycle K L 1) (z : K.X (-1)) :
    rawSourceCocycleMap x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((x.val.v (-1) 0 rfl).hom z) := by
  change cochainCokernelLinearEquiv L
    (sourceCocycleMap x ((rawSyzygyEquiv K).symm (Submodule.Quotient.mk z))) = _
  rw [rawSyzygyEquiv_symm_mk, sourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk
    ((L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom
      ((sourceCocycleComponent x).hom
        ((K.extendXIso negIndexEmbedding (i := -1) (i' := 1) rfl).inv.hom z))) = _
  simp [sourceCocycleComponent]

variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (κ : H ⟶ mappingCone φ)

include k in

theorem rawSourceCocycleMap_cone (hi : Function.Injective (cochainCokernelMap φ)) :
    rawSourceCocycleMap (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ)) =
      coneLiftKernel φ κ hi := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (H.d (-2) (-1)).hom) z
  erw [rawSourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk
    ((((Cochain.ofHom κ).comp (mappingCone.fst φ).val rfl).v (-1) 0 rfl).hom z) = _
  rw [Cochain.comp_v _ _ rfl (-1) (-1) 0 (by omega) (by omega), Cochain.ofHom_v]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_RawSourceStable
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

def rawSourceStableEquiv : CohomologyClass K L 1 ≃+ StableHom R (RawSyzygy K) (CochainCokernel L) :=
  (fullHomSourceStableLinearEquiv (k := k) K L 1 hK hL).toAddEquiv.trans
    (((StableIsomorphism.ofLinearEquiv (rawSyzygyEquiv K).symm).sourceAddEquiv).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv L)).targetAddEquiv)

@[simp]
theorem rawSourceStableEquiv_mk (x : Cocycle K L 1) :
    rawSourceStableEquiv (k := k) K L hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (rawSourceCocycleMap x) := by
  simp only [rawSourceStableEquiv, AddEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  erw [fullHomSourceStableLinearEquiv_mk hK hL x]
  rw [StableHom.comp_classOf, StableHom.comp_classOf]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_RawSourceDegrees
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

def rawCokernelAtEquiv : Cokernel (chainOfCochain K) n ≃ₗ[R] RawCokernelAt K n :=
  cokernelLinearCongr _ _
    (K.extendXIso negIndexEmbedding (i := -(n+1)) (i' := n+1) (neg_neg (n+1))).toLinearEquiv
    (K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).toLinearEquiv
    (congrArg ModuleCat.Hom.hom
      (reverseShortComplexIso K (-(n+1)) (-n) (-(n-1)) (n+1) n (n-1)
        (neg_neg (n+1)) (neg_neg n) (neg_neg (n-1))).hom.comm₁₂).symm

@[simp]
theorem rawCokernelAtEquiv_symm_mk (z : K.X (-n)) :
    (rawCokernelAtEquiv K n).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        ((K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).inv.hom z) := rfl

def rawCokernelAtInclusion : RawCokernelAt K (n+1) →ₗ[R] K.X (-n) :=
  (LinearMap.range (K.d (-(n+1+1)) (-(n+1))).hom).liftQ
    (K.d (-(n+1)) (-n)).hom
    (LinearMap.range_le_ker_iff.mpr
      (congrArg ModuleCat.Hom.hom (K.d_comp_d (-(n+1+1)) (-(n+1)) (-n))))

theorem rawCokernelAtInclusion_cover :
    ((LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ).comp
      (rawCokernelAtInclusion K n) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(n+1+1)) (-(n+1))).hom) z
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩

variable {k : Type u} [Field k] [Algebra k R]
variable {K n} {L M : CochainComplex (ModuleCat.{u} R) ℤ}

def rawSourceAt (x : Cocycle K L n) : RawCokernelAt K n →ₗ[R] CochainCokernel L :=
  (cochainCokernelLinearEquiv L).toLinearMap.comp
    ((sourceCocycleMap x).comp (rawCokernelAtEquiv K n).symm.toLinearMap)

include k in
@[simp]
theorem rawSourceAt_mk [CharP k 2] (x : Cocycle K L n) (z : K.X (-n)) :
    rawSourceAt x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((x.val.v (-n) 0 (by omega)).hom z) := by
  change cochainCokernelLinearEquiv L
    (sourceCocycleMap x ((rawCokernelAtEquiv K n).symm (Submodule.Quotient.mk z))) = _
  rw [rawCokernelAtEquiv_symm_mk, sourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk
    ((L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom
      ((sourceCocycleComponent x).hom
        ((K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).inv.hom z))) = _
  simp [sourceCocycleComponent]

include k in
theorem rawSourceAt_postcomp [CharP k 2] (x : Cocycle K L n) (f : L ⟶ M) :
    rawSourceAt (x.postcomp f) = (cochainCokernelMap f).comp (rawSourceAt x) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(n+1)) (-n)).hom) z
  change rawSourceAt (x.postcomp f) (Submodule.Quotient.mk z) =
    cochainCokernelMap f (rawSourceAt x (Submodule.Quotient.mk z))
  rw [rawSourceAt_mk (k := k), rawSourceAt_mk (k := k)]
  change Submodule.Quotient.mk
    (((x.val.comp (Cochain.ofHom f) (add_zero n)).v (-n) 0 (by omega)).hom z) = _
  rw [Cochain.comp_v _ _ (add_zero n) (-n) 0 0 (by omega) (by omega), Cochain.ofHom_v]
  rfl

def rawSourceAtStableEquiv (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L n ≃+ StableHom R (RawCokernelAt K n) (CochainCokernel L) :=
  (fullHomSourceStableLinearEquiv (k := k) K L n hK hL).toAddEquiv.trans
    (((StableIsomorphism.ofLinearEquiv (rawCokernelAtEquiv K n).symm).sourceAddEquiv).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv L)).targetAddEquiv)

@[simp]
theorem rawSourceAtStableEquiv_mk
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (x : Cocycle K L n) :
    rawSourceAtStableEquiv (k := k) K L n hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (rawSourceAt x) := by
  simp only [rawSourceAtStableEquiv, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  erw [fullHomSourceStableLinearEquiv_mk hK hL x]
  rw [StableHom.comp_classOf, StableHom.comp_classOf]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end


