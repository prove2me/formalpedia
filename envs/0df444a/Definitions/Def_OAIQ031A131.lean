-- Prove2me | Definitions.Def_OAIQ031A131
-- name    : OAIQ031A131
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:08:03.203023+00:00
-- url     : https://prove2.me/theorems/b51bb987-e593-4e16-9f65-937cba2d68d2
-- title:
--   Definitions bundle OAIQ031A131 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 4 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.pairSnd`, `OAI.ArExplicit.FrobeniusTrace.fullHomSourceDualityAt`, `OAI.ArExplicit.FullTate.negativeChart`, `OAI.ArExplicit.ModuleBar.cubicCocycle`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCubic.lean), [`AuslanderReiten_Bar_ModuleBarNative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNative.lean), [`AuslanderReiten_Bar_ModuleBarTensorProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorProducts.lean), [`AuslanderReiten_Cocycles_ReversedCocycleMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/ReversedCocycleMap.lean), [`AuslanderReiten_Complete_FullTateModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FullTateModel.lean), [`AuslanderReiten_HomComplex_FullHomSourceDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomSourceDuality.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProduct.lean), [`AuslanderReiten_Stable_TargetStableCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/TargetStableCoordinates.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A108`, `OAIQ031A119`, `OAIQ031A120` and `OAIQ031A124` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A141` and `OAIQ031A144`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A108
import Definitions.Def_OAIQ031A119
import Definitions.Def_OAIQ031A120
import Definitions.Def_OAIQ031A124

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def cubicCocycle : Cocycle (resolution k R M).cochainComplex (resolution k R M).cochainComplex 3 :=
  ResolutionProducts.natCubicCocycle (k := k) (resolution k R M) (cubicMap k R M p)
    (cubicMap_comm k R M p hp)

variable [HasDerivedCategory (ModuleCat.{u} R)]

theorem cubicCocycle_endExt :
    ResolutionProducts.endExt (resolution k R M) (cubicCocycle k R M p hp) =
      extClass3 k R M p hp := by
  have h := ResolutionProducts.natCubic_endExt_eq (k := k) (resolution k R M)
    (cubicMap k R M p) (cubicMap_comm k R M p hp)
  simp only [cubicMap_augmentation] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarNative
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

variable [HasDerivedCategory (ModuleCat.{u} R)]

theorem nativeCubicMap_class :
    ResolutionProducts.endExt (nativeResolution k R M)
      (ResolutionProducts.natCubicCocycle (k := k) (nativeResolution k R M)
        (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp)) =
      (extClass3 k R M p hp : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3) :=
  cubicCocycle_endExt k R M p hp

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

theorem nativeTensorCubics_commute :
    (nativeTensorFirst k R S M N p hp).comp (nativeTensorSecond k R S M N r hr) rfl =
      (nativeTensorSecond k R S M N r hr).comp (nativeTensorFirst k R S M N p hp) rfl :=
  ExternalTensor.cubicExt_commute k R S (nativeResolution k R M) (nativeResolution k S N)
    (nativeCubicMap k R M p) (nativeCubicMap k S N r)
    (nativeCubicMap_comm k R M p hp) (nativeCubicMap_comm k S N r hr)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_ReversedCocycleMap
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem sourceCocycleMap_eq_reversed (x : Cocycle K L n) :
    sourceCocycleMap x = reversedCokernelMap (k := k) x n 0 (by omega) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    rw [sourceCocycleMap_mk (k := k), reversedCokernelMap_mk]
    rfl

omit k [Field k] [Algebra k R] [CharP k 2] in
theorem reversedComponent_product (x : Cochain K L n) (y : Cochain L M m)
    (a b c : ℤ) (hab : a=n+b) (hbc : b=m+c) :
    reversedComponent (x.comp y rfl) a c (by omega) =
      reversedComponent x a b hab ≫ reversedComponent y b c hbc := by
  simp only [reversedComponent, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Cochain.comp_v x y rfl (-a) (-b) (-c) (by omega) (by omega)]
  simp only [Category.assoc]

theorem reversedCokernelMap_product (x : Cocycle K L n) (y : Cocycle L M m)
    (a b c : ℤ) (hab : a=n+b) (hbc : b=m+c) :
    reversedCokernelMap (k := k) (cocycleProduct x y) a c (by omega) =
      (reversedCokernelMap (k := k) y b c hbc).comp (reversedCokernelMap (k := k) x a b hab) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    simp only [LinearMap.comp_apply, reversedCokernelMap_mk]
    exact congrArg Submodule.Quotient.mk
      (congrArg (fun f => f.hom z) (reversedComponent_product x.val y.val a b c hab hbc))

theorem reversedCokernelMap_syzygy (x : Cocycle K L n)
    (hK : ExactProjectiveComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L))
    (a b : ℤ) (hab : a=n+b) :
    (syzygyInclusion hL b).comp (reversedCokernelMap (k := k) x (a+1) (b+1) (by omega)) =
      (reversedComponent x.val a b hab).hom.comp (syzygyInclusion hK a) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    simp only [LinearMap.comp_apply, reversedCokernelMap_mk, syzygyInclusion_mk]
    exact congrArg (fun f => f.hom z) (reversedComponent_comm (k := k) x a b hab)

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_TargetStableCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem targetCocycleMap_mk (x : Cocycle K L n) (b : ℤ) (hb : n = -b)
    (z : (chainOfCochain K).X 0) :
    targetCocycleMap x b hb (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((reversedComponent x.val 0 b (by omega)).hom z) := by
  change shiftedCokernelEquiv L n b hb
    (Submodule.Quotient.mk (((cocycleComparisonMap x).f 0).hom z)) = _
  rw [shiftedCokernelEquiv_mk]
  congr 1
  unfold cocycleComparisonMap
  rw [extendMap_f _ negIndexEmbedding (show negIndexEmbedding.f 0 = 0 from rfl)]
  rw [cocycleHom_component]
  have he :
      (K.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom ≫
        x.val.v 0 (0+n) rfl ≫
          ((L⟦n⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).inv ≫
            (shiftedCokernelComponent L n b hb).hom = reversedComponent x.val 0 b (by omega) := by
    subst n
    dsimp only [shiftedCokernelComponent, reversedComponent]
    erw [Iso.trans_hom, Iso.trans_hom]
    simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
    simp only [CochainComplex.shiftFunctorObjXIso, Int.neg_zero]
    erw [Iso.inv_hom_id_assoc, component_transport_assoc]
    all_goals simp
  exact congrArg (fun f => f.hom z) he

variable [CharP k 2]
include k

theorem targetCocycleMap_eq_reversed (x : Cocycle K L n) (b : ℤ) (hb : n = -b) :
    targetCocycleMap x b hb = reversedCokernelMap (k := k) x 0 b (by omega) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    rw [targetCocycleMap_mk, reversedCokernelMap_mk]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomSourceDuality
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
namespace ArExplicit.FrobeniusTrace
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b)=τ.trace (b*a))
open CompleteComparison
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

def fullHomSourceDualityAt (a b : ℤ) (hb : b = -a-1) :
    Module.Dual k (CohomologyClass K K a) ≃ₗ[k] CohomologyClass K K b :=
  (fullHomSourceStableLinearEquiv (k := k) K K a hK
    hK.toExactProjectiveComplex).symm.dualMap |>.trans
      ((τ.completeStableDualityAt hs (chainOfCochain K) hK.toExactProjectiveComplex a).trans
        (fullHomTargetStableLinearEquiv (k := k) (a+1) (by omega) hK
          hK.toExactProjectiveComplex).symm)

theorem fullHomSourceDualityAt_symm_apply (a b : ℤ) (hb : b = -a-1)
    (v : CohomologyClass K K b) (u : CohomologyClass K K a) :
    ((τ.fullHomSourceDualityAt hs K hK a b hb).symm v) u =
      ((τ.completeStableDualityAt hs (chainOfCochain K) hK.toExactProjectiveComplex a).symm
        (fullHomTargetStableLinearEquiv (k := k) (a+1) (by omega) hK
          hK.toExactProjectiveComplex v))
        (fullHomSourceStableLinearEquiv (k := k) K K a hK hK.toExactProjectiveComplex u) := rfl

variable [CharP k 2]

theorem fullHomSourceDualityAt_product (a n m : ℤ) (hm : m = -(n+a)-1)
    (p : CohomologyClass K K n) (u : CohomologyClass K K a)
    (v : CohomologyClass K K m) :
    ((τ.fullHomSourceDualityAt hs K hK a (m+n) (by omega)).symm
      (fullHomProduct v p)) u =
    ((τ.fullHomSourceDualityAt hs K hK (n+a) m hm).symm v)
      (fullHomProduct p u) := by
  obtain ⟨p,rfl⟩ := CohomologyClass.mk_surjective p
  obtain ⟨u,rfl⟩ := CohomologyClass.mk_surjective u
  obtain ⟨v,rfl⟩ := CohomologyClass.mk_surjective v
  rw [fullHomProduct_mk, fullHomProduct_mk,
    fullHomSourceDualityAt_symm_apply, fullHomSourceDualityAt_symm_apply,
    fullHomTargetStableLinearEquiv_mk, fullHomTargetStableLinearEquiv_mk,
    fullHomSourceStableLinearEquiv_mk, fullHomSourceStableLinearEquiv_mk]
  rw [targetCocycleMap_eq_reversed (k := k), targetCocycleMap_eq_reversed (k := k),
    sourceCocycleMap_eq_reversed (k := k), sourceCocycleMap_eq_reversed (k := k),
    reversedCokernelMap_product (k := k) v p 0 (n+a+1) (a+1) (by omega) (by omega),
    reversedCokernelMap_product (k := k) p u (n+a) a 0 (by omega) (by omega)]
  exact (τ.completeStableDualityAt_source hs hK.toExactProjectiveComplex
    hK.toExactProjectiveComplex (n+a) a
    (reversedComponent p.val (n+a) a (by omega)).hom
    (reversedCokernelMap (k := k) p (n+a) a (by omega))
    (reversedCokernelMap (k := k) p (n+a+1) (a+1) (by omega))
    (by ext x; rfl) (reversedCokernelMap_syzygy (k := k) p hK.toExactProjectiveComplex
      hK.toExactProjectiveComplex (n+a) a (by omega))
    (StableHom.classOf R _ _ (reversedCokernelMap (k := k) u a 0 (by omega)))
    (StableHom.classOf R _ _ (reversedCokernelMap (k := k) v 0 (n+a+1) (by omega)))).symm

end ArExplicit.FrobeniusTrace

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
local notation "H" => CohomologyClass K K

variable {K}

def negativeChart (positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n)
    (n : ℕ) : H (-1-3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.DualPiece k n :=
  (τ.fullHomSourceDualityAt hs K hK (3*(n:ℤ)) (-1-3*(n:ℤ)) (by omega)).symm.trans
    (positive n).symm.dualMap

omit [CharP k 2] in
theorem negativeChart_transport_apply
    (positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n)
    (a : ℤ) (n : ℕ) (ha : a=-1-3*(n:ℤ)) (v : H a) (w : BinaryKoszul.Piece k n) :
    negativeChart τ hs hK positive n (degreeEquiv (k := k) H ha v) w =
      ((τ.fullHomSourceDualityAt hs K hK (3*(n:ℤ)) a (by omega)).symm v)
        ((positive n).symm w) := by
  subst a
  rfl

omit [CharP k 2] in
theorem duality_source_transport {a a' b : ℤ} (h : a=a')
    (hb : b=-a-1) (hb' : b=-a'-1) (v : H b) (u : H a) :
    ((τ.fullHomSourceDualityAt hs K hK a b hb).symm v) u =
      ((τ.fullHomSourceDualityAt hs K hK a' b hb').symm v) (degreeEquiv (k := k) H h u) := by
  subst a'
  rfl

theorem negativeChart_action
    (positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n)
    (p : H 3) (op : ∀ n, BinaryKoszul.Piece k n →ₗ[k] BinaryKoszul.Piece k (n+1))
    (hp : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
      positive (n+1) (degreeEquiv (k := k) H (show 3+a=3*((n+1:ℕ):ℤ) by omega)
        (fullHomProduct p v)) = op n (positive n (degreeEquiv (k := k) H ha v)))
    (a : ℤ) (n : ℕ) (ha : a=-1-3*((n+1:ℕ):ℤ)) (v : H a) :
    negativeChart τ hs hK positive n
      (degreeEquiv (k := k) H (show a+3=-1-3*(n:ℤ) by omega) (fullHomProduct v p)) =
      (op n).dualMap (negativeChart τ hs hK positive (n+1) (degreeEquiv (k := k) H ha v)) := by
  apply LinearMap.ext
  intro w
  rw [negativeChart_transport_apply]
  rw [τ.fullHomSourceDualityAt_product hs K hK (3*(n:ℤ)) 3 a (by omega)]
  rw [duality_source_transport τ hs hK (show 3+3*(n:ℤ)=3*((n+1:ℕ):ℤ) by omega)
    (by omega) (by omega)]
  change _ = negativeChart τ hs hK positive (n+1) (degreeEquiv (k := k) H ha v) (op n w)
  rw [negativeChart_transport_apply]
  congr 1
  apply (positive (n+1)).injective
  rw [hp _ n rfl]
  simp [degreeEquiv]

end ArExplicit.FullTate

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionProduct
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N : FiniteLeftModule k R}

variable (M N)

def pairSnd : (pairModule M N).carrier →ₗ[R] N.carrier := LinearMap.snd R _ _

end ArExplicit.FiniteLeftModule

end

end OAI
end


