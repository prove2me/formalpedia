-- Prove2me | Definitions.Def_OAIQ031A082
-- name    : OAIQ031A082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:22:36.402446+00:00
-- url     : https://prove2.me/theorems/8e4a2e73-0dc0-4b33-bf67-28984e3390d9
-- title:
--   Definitions bundle OAIQ031A082 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions, 1 instance and 8 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.piRight`, `OAI.ArExplicit.Induction.homEquiv`, `OAI.ArExplicit.Induction.restrictHom`, `OAI.ArExplicit.TrivialInduction.quotientComplexIso`, `OAI.ArExplicit.TrivialInduction.quotientEquiv`, `OAI.ArExplicit.TrivialInduction.quotientFunctorIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarProjective.lean), [`AuslanderReiten_Cocycles_CocycleDetector`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleDetector.lean), [`AuslanderReiten_Ext_TExtRecurrence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtRecurrence.lean), [`AuslanderReiten_Homology_VectorCochainKunnethLiteral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethLiteral.lean), [`AuslanderReiten_Modules_InductionAdjunction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/InductionAdjunction.lean), [`AuslanderReiten_Modules_TInducedHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TInducedHom.lean), [`AuslanderReiten_Modules_TInductionHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TInductionHomology.lean), [`AuslanderReiten_Resolutions_TrivialInductionComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionComplex.lean), [`AuslanderReiten_Resolutions_TrivialInductionQuotient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionQuotient.lean), [`AuslanderReiten_Stable_StableExtEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExtEquiv.lean), [`AuslanderReiten_Tensor_BalancedTensorPi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorPi.lean), [`AuslanderReiten_Tensor_BalancedTensorProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorProjective.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A063`, `OAIQ031A064`, `OAIQ031A065`, `OAIQ031A066` and `OAIQ031A067` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A094`, `OAIQ031A096`, `OAIQ031A097`, `OAIQ031A102` and `OAIQ031A104`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A064
import Definitions.Def_OAIQ031A065
import Definitions.Def_OAIQ031A066
import Definitions.Def_OAIQ031A067

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

theorem projective (n : ℕ) : Module.Projective (Enveloping k R) (moduleObject k R (n + 1)) := by
  let := free k R n
  infer_instance

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

theorem hom_tmul_t (hq1 : 1 + q ≠ 0)
    (g : ModuleBar.moduleObject k R S 3 →ₗ[R] ModuleBar.moduleObject k R S 0)
    (x : ModuleBar.object k R S 2) :
    g (T.vector q (false, .t) ⊗ₜ[k] x) = 0 := by
  have he := g.map_smul (T.vector q (false, .t))
    ((1 : R) ⊗ₜ[k] x : ModuleBar.moduleObject k R S 3)
  change g ((T.vector q (false, .t) * 1) ⊗ₜ[k] x) = _ at he
  rw [mul_one] at he
  rw [he]
  change T.vector q (false, .t) • (g ((1 : R) ⊗ₜ[k] x) : S) = 0
  convert! vector_smul_simple q hq1 (false, .t) (g ((1 : R) ⊗ₜ[k] x) : S) using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorPi
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Algebra k R] [Ring S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def piRight : BalancedTensor k R F (ι → M) ≃ₗ[S] (ι → BalancedTensor k R F M) where
  __ := piRightMap
  invFun := piRightInv
  right_inv z := by
    ext i
    change piRightMap (S := S) (∑ j, mapRight (k := k) (S := S) (LinearMap.single R (fun _ : ι => M) j) (z j)) i = z i
    simp only [map_sum, Finset.sum_apply, piRightMap_single]
    simp
  left_inv z := by
    change piRightInv (S := S) (piRightMap (S := S) z) = z
    induction z using induction_on with
    | zero => simp
    | tmul f m =>
      change (∑ i, tmul (k := k) (R := R) f (Pi.single i (m i))) = tmul f m
      rw [← tmul_sum]
      congr
      exact Finset.univ_sum_single m
    | add x y hx hy => simp only [map_add, hx, hy]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

theorem projective [Module.Projective S F] [Module.Finite R M] [Module.Projective R M] :
    Module.Projective S (BalancedTensor k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let : Module.Projective S (BalancedTensor k R F R) :=
    Module.Projective.of_equiv (runitLeft (k := k) (R := R) (S := S) (F := F)).symm
  let : Module.Projective S (BalancedTensor k R F (Fin n → R)) :=
    Module.Projective.of_equiv (piRight (k := k) (R := R) (S := S) (F := F) (M := R)).symm
  apply Module.Projective.of_split (mapRight (k := k) (S := S) s) (mapRight (k := k) (S := S) p)
  rw [← mapRight_comp, hs, mapRight_id]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionAdjunction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
namespace Induction

variable {k R S V W : Type*} [CommRing k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S] (ι : R →ₐ[k] S)
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [Module S W]
  [IsScalarTower k R W] [IsScalarTower k S W]

def restrictHom (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w)
    (f : Object (V := V) ι →ₗ[S] W) : V →ₗ[R] W where
  toFun v := f (BalancedTensor.tmul ⟨1⟩ v)
  map_add' x y := by rw [BalancedTensor.tmul_add, map_add]
  map_smul' r v := by
    rw [← BalancedTensor.balance]
    change f (BalancedTensor.tmul ⟨1 * ι r⟩ v) = r • f (BalancedTensor.tmul ⟨1⟩ v)
    rw [one_mul, hcompat]
    have he : BalancedTensor.tmul (InductionBimodule.mk (ι r)) v =
        (ι r) • (BalancedTensor.tmul (InductionBimodule.mk (1 : S)) v : Object (V := V) ι) := by
      change BalancedTensor.tmul (InductionBimodule.mk (ι r)) v =
        BalancedTensor.tmul (InductionBimodule.mk (ι r * 1)) v
      rw [mul_one]
    rw [he, f.map_smul]

def homEquiv (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w) :
    (Object (V := V) ι →ₗ[S] W) ≃ₗ[k] (V →ₗ[R] W) where
  toFun := restrictHom ι hcompat
  invFun := extendHom ι hcompat
  left_inv f := by
    apply BalancedTensor.leftHom_ext
    intro a v
    change a.value • f (BalancedTensor.tmul ⟨1⟩ v) = f (BalancedTensor.tmul a v)
    rw [← f.map_smul]
    congr 1
    change BalancedTensor.tmul ⟨a.value * 1⟩ v = BalancedTensor.tmul a v
    rw [mul_one]
  right_inv g := by
    apply LinearMap.ext
    intro v
    exact one_smul S (g v)
  map_add' f g := by
    apply LinearMap.ext
    intro v
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro v
    rfl

end Induction
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionComplex
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

variable {ι : Type*} {c : ComplexShape ι}

instance induced_term_projective (P : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)] :
    Module.Projective T ((inducedComplex (k := k) P).X i) :=
  BalancedTensor.projective

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionQuotient
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

def quotientEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (Quotient (k := k) (R := R)) M ≃ₗ[T] (inflate (k := k)).obj M where
  toFun := quotientScalarMap M
  invFun m := BalancedTensor.tmul ⟨1⟩ m
  left_inv z := by
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, BalancedTensor.tmul_add] using congrArg₂ (· + ·) hx hy
    | tmul r m =>
      change BalancedTensor.tmul (InductionBimodule.mk (1 : R)) (r.value • m) =
        BalancedTensor.tmul r m
      rw [← BalancedTensor.balance]
      change BalancedTensor.tmul (InductionBimodule.mk (1 * r.value)) m = _
      rw [one_mul]
  right_inv m := by
    exact @one_smul R M _ _ (show M from m)
  map_add' := (quotientScalarMap M).map_add
  map_smul' t z := by
    change quotientScalarMap M (t • z) = t.base • quotientScalarMap M z
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | tmul r m => exact mul_smul t.base r.value m
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def quotientFunctorIso :
    BalancedTensor.functor (k := k) (R := R) (S := T) (F := Quotient (k := k) (R := R)) ≅ inflate :=
  NatIso.ofComponents (fun M => (quotientEquiv M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.leftHom_ext
    intro r m
    change r.value • f.hom m = f.hom (r.value • m)
    exact (f.hom.map_smul r.value m).symm)

def quotientComplexIso {ι : Type*} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{u} R) c) :
    quotientComplex (k := k) P ≅ ((inflate (k := k)).mapHomologicalComplex c).obj P :=
  (NatIso.mapHomologicalComplex quotientFunctorIso c).app P

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInductionHomology
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

theorem tQuotient_exact (h : NoPositivePowerOne q) (n : ℕ) (hn : n ≠ 0) :
    (TrivialInduction.quotientComplex (k := k) (complex q)).ExactAt n := by
  apply (exactAt_iff_of_quasiIsoAt
    (TrivialInduction.quotientComplexIso (complex q)).hom n).mpr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ModuleRestriction.map_exact _ _ (complex_exactAt_succ q h m)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInducedHom
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
local notation "C" => BaseAlgebra k q
local notation "T" => ArExplicit.T k q

theorem tInduced_term_hom_zero (hq1 : 1 + q ≠ 0) (n : ℕ)
    (f : (TrivialInduction.inducedComplex (k := k) (complex q)).X (n + 1) ⟶
      ModuleCat.of T (Simple q)) : f = 0 := by
  let := moduleCatBaseModule (k := k) (R := C) ((complex q).X (n + 1))
  let := moduleCatBaseTower (k := k) (R := C) ((complex q).X (n + 1))
  let e := Induction.homEquiv (V := (complex q).X (n + 1)) (W := Simple q)
    (TrivialExtension.inlHom (k := k) (A := C)) (fun _ _ => rfl)
  apply ModuleCat.hom_ext
  exact e.injective ((hom_E_simple_eq_zero q hq1 (e f.hom)).trans (e.map_zero).symm)

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

omit [CharP k 2] in
theorem tSimpleDerived_negative_zero (n : ℤ) (hn : n < 0)
    (f : tSimpleDerived q ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  let : (tSimpleDerived q).IsLE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))).IsLE 0)
  let : (tSimpleDerived q).IsGE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))).IsGE 0)
  let : ((tSimpleDerived q)⟦n⟧).IsGE (-n) :=
    DerivedCategory.TStructure.t.isGE_shift (tSimpleDerived q) 0 n (-n) (by omega)
  exact DerivedCategory.TStructure.t.zero f 0 (-n) (by omega)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethLiteral
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

theorem kunnethLinearEquiv_literal_tmul (i j n : ℕ) (hij : i+j=n)
    (x : LinearMap.ker (P.d i (i+1)).hom) (y : LinearMap.ker (Q.d j (j+1)).hom)
    (z : LinearMap.ker ((mapBifunctor P Q T (.up ℕ)).d n (n+1)).hom)
    (hz : z.val = (ιMapBifunctor P Q T (.up ℕ) i j n hij).hom (x.val ⊗ₜ[k] y.val)) :
    kunnethLinearEquiv k T P Q n (literalClass k (mapBifunctor P Q T (.up ℕ)) n z) =
      (DFinsupp.single ⟨(i,j), hij⟩ (literalClass k P i x ⊗ₜ[k] literalClass k Q j y) :
        Π₀ p : {p : ℕ × ℕ // p.1+p.2=n},
          (P.homology p.val.1 ⊗[k] Q.homology p.val.2)) := by
  let xc := (literalCyclesIso k P i).inv.hom x
  let yc := (literalCyclesIso k Q j).inv.hom y
  let t := (ιMapBifunctor (gradedCycles k P) (gradedCycles k Q) T (.up ℕ) i j n hij).hom
    (xc ⊗ₜ[k] yc)
  have ht : ((mapBifunctor (gradedCycles k P) (gradedCycles k Q) T (.up ℕ)).d n (n+1)).hom t = 0 := by
    rw [total_zero_differential]
    rfl
  let tc : LinearMap.ker ((mapBifunctor (gradedCycles k P) (gradedCycles k Q) T (.up ℕ)).d n (n+1)).hom := ⟨t, ht⟩
  have hm : ((mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) T (.up ℕ)).f n).hom t = z.val := by
    have h := congrArg (fun f => f.hom (xc ⊗ₜ[k] yc))
      (ι_mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) T (.up ℕ) i j n hij)
    change _ = (ιMapBifunctor P Q T (.up ℕ) i j n hij).hom
      ((P.iCycles i).hom xc ⊗ₜ[k] (Q.iCycles j).hom yc) at h
    rw [show (P.iCycles i).hom xc = x.val from literalCyclesIso_inv_iCycles k P i x,
      show (Q.iCycles j).hom yc = y.val from literalCyclesIso_inv_iCycles k Q j y] at h
    exact h.trans hz.symm
  change (ModuleCat.coprodIsoDirectSum _).hom.hom
    ((kunnethIso k T P Q n).hom.hom (literalClass k _ n z)) = _
  rw [kunneth_literal_cycles k T P Q n tc z hm]
  have hq := congrArg (fun f => f.hom (xc ⊗ₜ[k] yc))
    (ι_mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) T (.up ℕ) i j n hij)
  change _ = (ιMapBifunctor (gradedHomology k P) (gradedHomology k Q) T (.up ℕ) i j n hij).hom
    (literalClass k P i x ⊗ₜ[k] literalClass k Q j y) at hq
  change (ModuleCat.coprodIsoDirectSum _).hom.hom
    (((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) T (.up ℕ)).f n).hom t) = _
  change ((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) T (.up ℕ)).f n).hom t =
    (ιMapBifunctor (gradedHomology k P) (gradedHomology k Q) T (.up ℕ) i j n hij).hom
      (literalClass k P i x ⊗ₜ[k] literalClass k Q j y) at hq
  erw [hq]
  have hi := ModuleCat.ι_coprodIsoDirectSum_hom
    (fun p : {p : ℕ × ℕ // p.1+p.2=n} => ((T).obj (P.homology p.val.1)).obj (Q.homology p.val.2))
    ⟨(i,j), hij⟩
  exact congrArg (fun f => (ModuleCat.Hom.hom f)
    (literalClass k P i x ⊗ₜ[k] literalClass k Q j y)) hi

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExtEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
open CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : TotallyAcyclicComplex P)
variable (N : ModuleCat.{u} R)

theorem positiveExtStableEquiv_extMk (n : ℕ)
    (f : (completeExtResolution hP).complex.X (n+1) ⟶ N)
    (hf : (completeExtResolution hP).complex.d (n+2) (n+1) ≫ f = 0) :
    positiveExtStableEquiv (k := k) hP N n
      ((completeExtResolution hP).extMk f (n+2) rfl hf) =
        completeExtCyclesStable (k := k) hP N n ⟨f,hf⟩ := by
  let z : LinearMap.ker (ResolutionHomology.differential (k := k) (Y := N)
    (completeExtResolution hP) (n+1)) := ⟨f,hf⟩
  have he : ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n
      (Submodule.Quotient.mk z) = (completeExtResolution hP).extMk f (n+2) rfl hf := rfl
  rw [← he]
  change completeExtHomologyStableEquiv hP N n
    ((ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n).symm
      ((ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n)
        (Submodule.Quotient.mk z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end ArExplicit

end

end OAI
end


