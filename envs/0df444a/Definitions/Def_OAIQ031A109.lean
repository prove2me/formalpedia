-- Prove2me | Definitions.Def_OAIQ031A109
-- name    : OAIQ031A109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:44:20.852095+00:00
-- url     : https://prove2.me/theorems/baeaceba-1b73-4926-86b9-7dd34ed2bb3e
-- title:
--   Definitions bundle OAIQ031A109 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 6 definitions and 13 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.twistedResolution`, `OAI.ArExplicit.BarBalanced.canonicalMap`, `OAI.ArExplicit.BarBalanced.canonicalTermIso`, `OAI.ArExplicit.BarBalanced.cubicHom`, `OAI.ArExplicit.CompleteComparison.cokernelCochainLift`, `OAI.ArExplicit.CompleteComparison.rawCokernelHomotopyIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedCanonical.lean), [`AuslanderReiten_Bar_CanonicalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarEvaluation.lean), [`AuslanderReiten_Bar_TwistedBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBar.lean), [`AuslanderReiten_Cocycles_SourceCocycleNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/SourceCocycleNaturality.lean), [`AuslanderReiten_Complete_CompleteCokernelLifts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteCokernelLifts.lean), [`AuslanderReiten_Cones_CochainCokernelIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CochainCokernelIso.lean), [`AuslanderReiten_Ext_ExtTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtTensorAction.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicExt.lean), [`AuslanderReiten_Tensor_ExternalTensorHomCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomCubic.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A092`, `OAIQ031A093`, `OAIQ031A095`, `OAIQ031A096` and `OAIQ031A097` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A120`, `OAIQ031A121`, `OAIQ031A122` and `OAIQ031A123`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A092
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A095
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A097

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

@[simp] theorem canonicalEquiv_tmul (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) (x : X) :
    canonicalEquiv k R X n (BalancedTensor.tmul z x) =
      rawEval k R X n (z.value ⊗ₜ[k] x) := by
  change equiv k R X n (canonicalTransport k R X n (BalancedTensor.tmul z x)) = _
  rw [canonicalTransport_tmul]
  rfl

def canonicalMap {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n) :
    canonicalEvaluated k R X m →ₗ[R] canonicalEvaluated k R X n :=
  EnvelopingBimodule.tensorMap X f

@[simp] theorem canonicalMap_tmul {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R m)) (x : X) :
    canonicalMap k R X f (BalancedTensor.tmul z x) =
      BalancedTensor.tmul (EnvelopingBimodule.map f z) x := rfl

/-- Naming this morphism keeps kernel checking from repeatedly expanding the
iterated tensor-module structures at successor degrees. -/
abbrev cubicHom (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    AbsoluteBar.moduleObject k R (n+4) ⟶ AbsoluteBar.moduleObject k R (n+1) :=
  ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+4))
    (Y := AbsoluteBar.moduleObject k R (n+1)) (AbsoluteBar.suffixComparisonMap k R p n)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarEvaluation
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

def canonicalTermIso (n : ℕ) :
    (ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R)).X n ≅
      (ModuleBar.complex k R X).X n :=
  (canonicalEquiv k R X (n+1)).toModuleIso

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

def twistedResolution (h : R ≃ₐ[k] R) : ProjectiveResolution (twistedObject k R h 0) where
  complex := twistedComplex k R h
  projective n := by
    let := twistedProjective k R h n
    exact (twistedObject k R h (n + 1)).projective_of_categoryTheory_projective
  π := twistedAugmentation k R h
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((twistedComplex k R h).d 1 0).hom =
            LinearMap.ker ((twistedAugmentation k R h).f 0).hom
          rw [twistedComplex_d, twistedAugmentation_zero]
          exact twistedDifferential_exact k R h 0
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact ⟨contraction k R 0 x, augmentation_contraction k R x⟩
      · exact (twistedComplex k R h).shape 0 0 (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact twistedComplex_exactAt k R h n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.AbsoluteBar

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

theorem sourceCocycleComponent_precomp (f : K ⟶ L) (x : Cocycle L M n) :
    sourceCocycleComponent (x.precomp f) =
      (extendMap f negIndexEmbedding).f n ≫ sourceCocycleComponent x := by
  unfold sourceCocycleComponent
  change _ ≫ ((Cochain.ofHom f).comp x.val (zero_add n)).v (-n) 0 (by omega) ≫ _ = _
  rw [Cochain.comp_v _ _ (zero_add n) (-n) (-n) 0 (by omega) (by omega),
    Cochain.ofHom_v,
    extendMap_f f negIndexEmbedding (i := -n) (i' := n) (neg_neg n)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem sourceCocycleComponent_postcomp (x : Cocycle K L n) (f : L ⟶ M) :
    sourceCocycleComponent (x.postcomp f) =
      sourceCocycleComponent x ≫ (extendMap f negIndexEmbedding).f 0 := by
  unfold sourceCocycleComponent
  change _ ≫ (x.val.comp (Cochain.ofHom f) (add_zero n)).v (-n) 0 (by omega) ≫ _ = _
  rw [Cochain.comp_v _ _ (add_zero n) (-n) 0 0 (by omega) (by omega),
    Cochain.ofHom_v, extendMap_f f negIndexEmbedding (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CochainCokernelIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

def rawCokernelHomotopyIso (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).obj K ≅ (HomotopyCategory.quotient _ _).obj L where
  hom := (cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex).symm
    (StableHom.classOf R _ _ e.toLinearMap)
  inv := (cochainHomotopyRawEquiv hL.to_chain hK.to_chain.toExactProjectiveComplex).symm
    (StableHom.classOf R _ _ e.symm.toLinearMap)
  hom_inv_id := by
    apply (cochainHomotopyRawEquiv hK.to_chain hK.to_chain.toExactProjectiveComplex).injective
    rw [cochainHomotopyRawEquiv_comp hK hL hK.toExactProjectiveCochain,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, StableHom.comp_classOf,
      rawEquiv_identity hK]
    exact congrArg (StableHom.classOf R _ _) e.symm_comp
  inv_hom_id := by
    apply (cochainHomotopyRawEquiv hL.to_chain hL.to_chain.toExactProjectiveComplex).injective
    rw [cochainHomotopyRawEquiv_comp hL hK hL.toExactProjectiveCochain,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, StableHom.comp_classOf,
      rawEquiv_identity hL]
    exact congrArg (StableHom.classOf R _ _) e.comp_symm

@[simp] theorem rawCokernelHomotopyIso_hom
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex
      (rawCokernelHomotopyIso hK hL e).hom = StableHom.classOf R _ _ e.toLinearMap :=
  AddEquiv.apply_symm_apply _ _

variable {K' L' : CochainComplex (ModuleCat.{u} R) ℤ}

theorem rawCokernelHomotopyIso_natural
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (hK' : TotallyAcyclicCochain K') (hL' : TotallyAcyclicCochain L')
    (e : CochainCokernel K ≃ₗ[R] CochainCokernel L)
    (e' : CochainCokernel K' ≃ₗ[R] CochainCokernel L')
    (a : K ⟶ K') (b : L ⟶ L')
    (hab : e'.toLinearMap.comp (cochainCokernelMap a) =
      (cochainCokernelMap b).comp e.toLinearMap) :
    (HomotopyCategory.quotient _ _).map a ≫ (rawCokernelHomotopyIso hK' hL' e').hom =
      (rawCokernelHomotopyIso hK hL e).hom ≫ (HomotopyCategory.quotient _ _).map b := by
  apply (cochainHomotopyRawEquiv hK.to_chain hL'.to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_comp hK hK' hL'.toExactProjectiveCochain,
    cochainHomotopyRawEquiv_comp hK hL hL'.toExactProjectiveCochain,
    cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    rawCokernelHomotopyIso_hom, rawCokernelHomotopyIso_hom,
    StableHom.comp_classOf, StableHom.comp_classOf, hab]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteCokernelLifts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
variable (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)

def cokernelCochainLift (p : CochainCokernel K →ₗ[R] CochainCokernel L) : K ⟶ L :=
  Classical.choose (cochainCokernelMap_surjective hK.to_chain
    hL.to_chain.toExactProjectiveComplex p)

@[simp] theorem cokernelCochainLift_map (p : CochainCokernel K →ₗ[R] CochainCokernel L) :
    cochainCokernelMap (cokernelCochainLift hK hL p) = p :=
  Classical.choose_spec (cochainCokernelMap_surjective hK.to_chain
    hL.to_chain.toExactProjectiveComplex p)

theorem cokernelCochainLift_quotient (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).map (cokernelCochainLift hK hL e.toLinearMap) =
      (rawCokernelHomotopyIso hK hL e).hom := by
  apply (cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cokernelCochainLift_map, rawCokernelHomotopyIso_hom]

theorem cokernelCochainLift_quotient_inv (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).map (cokernelCochainLift hL hK e.symm.toLinearMap) =
      (rawCokernelHomotopyIso hK hL e).inv := by
  apply (cochainHomotopyRawEquiv hL.to_chain hK.to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cokernelCochainLift_map]
  exact (AddEquiv.apply_symm_apply _ _).symm

theorem cokernelCochainLift_homotopy_inverse (e : CochainCokernel K ≃ₗ[R] CochainCokernel L) :
    (HomotopyCategory.quotient _ _).map
      (cokernelCochainLift hK hL e.toLinearMap ≫ cokernelCochainLift hL hK e.symm.toLinearMap) = 𝟙 _ := by
  rw [CategoryTheory.Functor.map_comp, cokernelCochainLift_quotient,
    cokernelCochainLift_quotient_inv, Iso.hom_inv_id]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

theorem elementary_secondCubic
    (r : ∀ n, Q.X (n+3) ⟶ Q.X n)
    (i j n : ℕ) (h : i+j=n) (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp (secondCubic k A B P Q r n) =
      elementaryHom k A B P Q U V i (j+3) (n+3) (by omega) f (g.comp (r j).hom) := by
  apply cubic_hom_ext k A B P Q (n+3)
  rintro ⟨⟨a,b⟩,hab⟩ x
  simp only [LinearMap.comp_apply, secondCubic_insert]
  rcases b with _ | (_ | (_ | b))
  · simp only [secondCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
      f (g.comp (r j).hom) a 0 hab (by intro he; have := congrArg Prod.snd he; omega) x).symm
  · simp only [secondCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
      f (g.comp (r j).hom) a 1 hab (by intro he; have := congrArg Prod.snd he; omega) x).symm
  · simp only [secondCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
      f (g.comp (r j).hom) a 2 hab (by intro he; have := congrArg Prod.snd he; omega) x).symm
  · by_cases hb : b=j
    · subst b
      have ha : a=i := by omega
      subst a
      simp only [secondCubicEntry, LinearMap.comp_apply, elementary_cubicInsert_same]
      exact map_second_comp k A B U V f g (r j).hom x
    · have hn : (a,b)≠(i,j) := by intro he; exact hb (congrArg Prod.snd he)
      have hn' : (a,b+3)≠(i,j+3) := by intro he; have := congrArg Prod.snd he; omega
      simp only [secondCubicEntry, LinearMap.comp_apply]
      rw [elementary_cubicInsert_ne k A B P Q U V i j n h f g a b (by omega) hn,
        elementary_cubicInsert_ne k A B P Q U V i (j+3) (n+3) (by omega)
          f (g.comp (r j).hom) a (b+3) hab hn']

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)

variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

omit [Module.Finite k A] [Module.Finite k B] in
theorem secondCubicExt_action {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : (projectiveResolution k A B P Q).complex.X n ⟶ N)
    (hf : (projectiveResolution k A B P Q).complex.d (n+1) n ≫ f=0) :
    (secondCubicExt k A B P Q r hr).comp ((projectiveResolution k A B P Q).extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
      (projectiveResolution k A B P Q).extMk (secondComparison k A B P Q r n ≫ f) (n+4) rfl
        (ResolutionProducts.cubicPrecomp_closed (projectiveResolution k A B P Q)
          (secondComparison k A B P Q r) (secondComparison_comm k A B P Q r hr) f hf) :=
  ResolutionProducts.cubic_endExt_comp_extMk (k := k) (projectiveResolution k A B P Q)
    (secondComparison k A B P Q r) (secondComparison_comm k A B P Q r hr) f hf

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtTensorAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)

variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)] in
theorem secondCubicExt_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    (secondCubicExt k A B P Q r hr).comp
      (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega : 3+n=n+3) =
      elementaryExt k A B P Q U V i (j+3) (n+3) (by omega) f (g.comp (r j).hom)
        hf (secondFactor_closed B Q V r hr j g hg) := by
  unfold elementaryExt
  erw [secondCubicExt_action]
  have he : secondComparison k A B P Q r n ≫
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
        (Y := moduleObject k A B U V) (elementaryHom k A B P.complex Q.complex U V i j n h f g) =
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X (n+3))
        (Y := moduleObject k A B U V)
        (elementaryHom k A B P.complex Q.complex U V i (j+3) (n+3) (by omega) f (g.comp (r j).hom)) :=
    ModuleCat.hom_ext (elementary_secondCubic k A B P.complex Q.complex U V r i j n h f g)
  exact extMk_of_eq (projectiveResolution k A B P Q) _ _ _ _ he

end ArExplicit.ExternalTensor

end

end OAI
end


