-- Prove2me | Definitions.Def_OAIQ031A093
-- name    : OAIQ031A093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:32:05.185189+00:00
-- url     : https://prove2.me/theorems/01223bca-9785-4592-83d5-26b8cc213433
-- title:
--   Definitions bundle OAIQ031A093 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 9 definitions, 1 instance and 9 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.fullHomSourceStableLinearEquiv`, `OAI.ArExplicit.CompleteComparison.fullHomStableLinearEquiv`, `OAI.ArExplicit.CompleteComparison.fullHomStableZeroLinearEquiv`, `OAI.ArExplicit.CompleteComparison.reversedComponent`, `OAI.ArExplicit.CompleteComparison.shiftedCokernelComponent`, `OAI.ArExplicit.CompleteComparison.shiftedCokernelEquiv`, `OAI.ArExplicit.CompleteComparison.sourceCocycleComponent`, `OAI.ArExplicit.CompleteComparison.sourceCocycleMap`, `OAI.ArExplicit.Resolution.homFRightLinearEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarSuffix.lean), [`AuslanderReiten_Bar_TwistedBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBar.lean), [`AuslanderReiten_Cocycles_ReversedCocycleMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/ReversedCocycleMap.lean), [`AuslanderReiten_Complete_CompleteShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShift.lean), [`AuslanderReiten_Complete_CompleteShiftDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShiftDual.lean), [`AuslanderReiten_Cones_CokernelShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelShift.lean), [`AuslanderReiten_Cones_CokernelShiftCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelShiftCoordinates.lean), [`AuslanderReiten_Duality_DualResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualResolution.lean), [`AuslanderReiten_HomComplex_FullHomLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomLinear.lean), [`AuslanderReiten_Stable_SourceStableCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/SourceStableCoordinates.lean), [`AuslanderReiten_Stable_SourceStableShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/SourceStableShift.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A078`, `OAIQ031A079` and `OAIQ031A080` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A105`, `OAIQ031A106`, `OAIQ031A107`, `OAIQ031A109`, `OAIQ031A110`, `OAIQ031A112`, `OAIQ031A114`, `OAIQ031A115` and `OAIQ031A117`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A079
import Definitions.Def_OAIQ031A080

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarSuffix
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

@[simp] theorem suffixComparison_succ_tmul (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (a : R) (x : object k R M (n + 3)) :
    suffixComparison k R M p (n + 1) (a ⊗ₜ[k] x) = a ⊗ₜ[k] suffixComparison k R M p n x := rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance twistedBaseModule (h : R ≃ₐ[k] R) (n : ℕ) : Module k (twistedObject k R h n) :=
  (object k R n).isModule

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomLinear
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u v

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
open scoped ModuleCat.Algebra

variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem cokernelMap_smul (a : k) (F : P ⟶ Q) (n : ℤ) :
    cokernelMap (a • F) n = a • cokernelMap F n := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) z
  change (LinearMap.range (Q.d (n + 1) n).hom).mkQ (a • (F.f n).hom x) =
    a • (LinearMap.range (Q.d (n + 1) n).hom).mkQ ((F.f n).hom x)
  exact ((LinearMap.range (Q.d (n + 1) n).hom).mkQ.restrictScalars k).map_smul a _

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

theorem cocycleComparisonMap_smul (a : k) (x : Cocycle K L n) :
    cocycleComparisonMap (a • x) = a • cocycleComparisonMap x := by
  unfold cocycleComparisonMap
  rw [cocycleHom_smul]
  apply HomologicalComplex.Hom.ext
  funext i
  have hi : negIndexEmbedding.f (-i) = i := neg_neg i
  simp only [HomologicalComplex.extendMap_f _ _ hi,
    HomologicalComplex.smul_f_apply, Linear.comp_smul, Linear.smul_comp]

theorem fullHomStableEquiv_smul (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧)))
    (a : k) (x : CohomologyClass K L n) :
    fullHomStableEquiv K L n hK hL (a • x) = a • fullHomStableEquiv K L n hK hL x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [← fullHom_mk_smul, fullHomStableEquiv_mk, fullHomStableEquiv_mk,
    cocycleComparisonMap_smul, cokernelMap_smul, StableHom.classOf_smul]

noncomputable def fullHomStableLinearEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧))) :
    CohomologyClass K L n ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain (L⟦n⟧)) 0) :=
  { fullHomStableEquiv K L n hK hL with
    map_smul' := fullHomStableEquiv_smul hK hL }

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShift
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace ExactProjectiveComplex

open CompleteComparison

theorem cochainShift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveComplex (chainOfCochain K)) (n : ℤ) :
    ExactProjectiveComplex (chainOfCochain (K⟦n⟧)) :=
  ((ExactProjectiveCochain.of_chain hK).shift n).to_chain

end ExactProjectiveComplex

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelShift
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]

noncomputable def shiftedCokernelEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a n : ℤ) (ha : a = -n) :
    Cokernel (chainOfCochain (K⟦a⟧)) 0 ≃ₗ[R] Cokernel (chainOfCochain K) n := by
  let E : (K⟦a⟧).opcycles 0 ≃ₗ[R] K.opcycles (-n) :=
    (ShortComplex.opcyclesMapIso
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by simpa using ha)).app K)).toLinearEquiv
  exact (cochainCokernelEquiv (K⟦a⟧) 0).trans
    (E.trans (cochainCokernelEquiv K n).symm)

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelShiftCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory HomologicalComplex
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]

noncomputable def shiftedCokernelComponent (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a n : ℤ) (ha : a = -n) :
    (chainOfCochain (K⟦a⟧)).X 0 ≅ (chainOfCochain K).X n :=
  (K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl ≪≫
    K.shiftFunctorObjXIso a 0 (-n) (by omega) ≪≫
      (K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).symm

@[simp]
theorem shiftedCokernelEquiv_mk (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a n : ℤ) (ha : a = -n) (x : (chainOfCochain (K⟦a⟧)).X 0) :
    shiftedCokernelEquiv K a n ha (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((shiftedCokernelComponent K a n ha).hom.hom x) := by
  apply (cochainCokernelEquiv K n).injective
  change cochainCokernelEquiv K n ((cochainCokernelEquiv K n).symm _) = _
  rw [LinearEquiv.apply_symm_apply, cochainCokernelEquiv_mk]
  erw [cochainCokernelEquiv_mk]
  have h := congrArg (fun f : (K⟦a⟧).X 0 ⟶ K.opcycles (-n) =>
      f.hom (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x))
    (ShortComplex.p_opcyclesMap
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by omega)).hom.app K))
  change (ShortComplex.opcyclesMap
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by omega)).hom.app K)).hom
      (((K⟦a⟧).pOpcycles 0).hom
        (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)) =
      (K.pOpcycles (-n)).hom
        ((K.shiftFunctorObjXIso a 0 (-n) (by omega)).hom.hom
          (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)) at h
  change (ShortComplex.opcyclesMap
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by omega)).hom.app K)).hom
      (((K⟦a⟧).pOpcycles 0).hom
        (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)) = _
  rw [h]
  congr 1
  change _ = (K.extendXIso negIndexEmbedding (neg_neg n)).hom.hom
    ((K.extendXIso negIndexEmbedding (neg_neg n)).inv.hom
      ((K.shiftFunctorObjXIso a 0 (-n) (by omega)).hom.hom
        (((K⟦a⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x)))
  exact (Iso.inv_hom_id_apply _ _).symm

@[simp]
theorem shiftedCokernelEquiv_symm_mk (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a n : ℤ) (ha : a = -n) (x : (chainOfCochain K).X n) :
    (shiftedCokernelEquiv K a n ha).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((shiftedCokernelComponent K a n ha).inv.hom x) := by
  apply (shiftedCokernelEquiv K a n ha).injective
  rw [LinearEquiv.apply_symm_apply, shiftedCokernelEquiv_mk]
  congr 1
  exact (Iso.inv_hom_id_apply _ _).symm

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace TotallyAcyclicComplex

open CompleteComparison

theorem cochainShift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K)) (a : ℤ) :
    TotallyAcyclicComplex (chainOfCochain (K⟦a⟧)) where
  toExactProjectiveComplex := hK.toExactProjectiveComplex.cochainShift a
  dualExact := ((DualExactCochain.of_chain hK).shift a).to_chain

end TotallyAcyclicComplex
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_SourceStableShift
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace ArExplicit.CompleteComparison

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]

noncomputable def fullHomStableZeroLinearEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L 0 ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0) :=
  (fullHomStableLinearEquiv K L 0 hK (hL.cochainShift 0)).trans
    (StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L 0 0 rfl))

noncomputable def fullHomSourceStableLinearEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L n ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) n) (Cokernel (chainOfCochain L) 0) :=
  (leftShiftCohomologyEquiv k K L n (-n) 0 (by omega)).trans
    ((fullHomStableZeroLinearEquiv (K⟦-n⟧) L (hK.cochainShift (-n)) hL).trans
      (StableHom.sourceEquiv (k := k) (shiftedCokernelEquiv K (-n) n rfl).symm))

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_SourceStableCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def sourceCocycleMap (x : Cocycle K L n) :
    Cokernel (chainOfCochain K) n →ₗ[R] Cokernel (chainOfCochain L) 0 :=
  (shiftedCokernelEquiv L 0 0 rfl).toLinearMap.comp
    ((cokernelMap (cocycleComparisonMap (x.leftShift (-n) 0 (by omega))) 0).comp
      (shiftedCokernelEquiv K (-n) n rfl).symm.toLinearMap)

@[simp]
theorem fullHomSourceStableLinearEquiv_mk
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (x : Cocycle K L n) :
    fullHomSourceStableLinearEquiv (k := k) K L n hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (sourceCocycleMap x) := by
  change StableHom.sourceEquiv (k := k) (shiftedCokernelEquiv K (-n) n rfl).symm
    (StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L 0 0 rfl)
      (fullHomStableEquiv (K⟦-n⟧) L 0 (hK.cochainShift (-n)) (hL.cochainShift 0)
        (CohomologyClass.mk (x.leftShift (-n) 0 (by omega))))) = _
  rw [fullHomStableEquiv_mk, StableHom.targetEquiv_classOf, StableHom.sourceEquiv_classOf]
  rfl

def sourceCocycleComponent (x : Cocycle K L n) :
    (chainOfCochain K).X n ⟶ (chainOfCochain L).X 0 :=
  (K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).hom ≫
    x.val.v (-n) 0 (by omega) ≫
      (L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).inv

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_ReversedCocycleMap
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def reversedComponent (x : Cochain K L n) (a b : ℤ) (hab : a=n+b) :
    (chainOfCochain K).X a ⟶ (chainOfCochain L).X b :=
  (K.extendXIso negIndexEmbedding (i := -a) (i' := a) (neg_neg a)).hom ≫
    x.v (-a) (-b) (by omega) ≫
      (L.extendXIso negIndexEmbedding (i := -b) (i' := b) (neg_neg b)).inv

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

def homFRightLinearEquiv : (F q →ₗ[C] C) ≃ₗ[Cᵐᵒᵖ] rightF q where
  __ := homFEquiv q
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

end ArExplicit.Resolution

end

end OAI
end


