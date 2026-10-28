-- Prove2me | Definitions.Def_OAIQ031A079
-- name    : OAIQ031A079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:20:57.033993+00:00
-- url     : https://prove2.me/theorems/ec618507-c054-4da8-ad13-fa1880a1040a
-- title:
--   Definitions bundle OAIQ031A079 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 8 definitions and 16 theorems. The definitions and types are `OAI.ArExplicit.A.stableEndEquiv`, `OAI.ArExplicit.AbsoluteBar.cochain3`, `OAI.ArExplicit.CompleteComparison.cochainCokernelEquiv`, `OAI.ArExplicit.CompleteComparison.cokernelOpcyclesEquiv`, `OAI.ArExplicit.Resolution.homFEquiv`, `OAI.ArExplicit.TwoCone.Data.restrict`, `OAI.ArExplicit.TwoCone.highLift`, `OAI.ArExplicit.TwoCone.termRestrictionEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarCasimir`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCasimir.lean), [`AuslanderReiten_Bar_BarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCochain.lean), [`AuslanderReiten_Bar_BarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarSuffix.lean), [`AuslanderReiten_Bar_TCasimirAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimirAugmentation.lean), [`AuslanderReiten_Complete_CompleteShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShift.lean), [`AuslanderReiten_Cones_CokernelShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelShift.lean), [`AuslanderReiten_Cones_CokernelShiftCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelShiftCoordinates.lean), [`AuslanderReiten_Cones_TwoConeRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeRestriction.lean), [`AuslanderReiten_Cones_TwoConeTail`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeTail.lean), [`AuslanderReiten_Duality_DualResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualResolution.lean), [`AuslanderReiten_Evaluation_TensorBeta`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorBeta.lean), [`AuslanderReiten_Stable_TensorStableEnd`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/TensorStableEnd.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A061`, `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A064` and `OAIQ031A065` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A092`, `OAIQ031A093`, `OAIQ031A095`, `OAIQ031A096`, `OAIQ031A102` and `OAIQ031A103`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A061
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A064
import Definitions.Def_OAIQ031A065

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCochain
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

theorem cochain3Linear_right (p : Cochain3 k R) (a : Rᵐᵒᵖ) (x : object k R 4) :
    cochain3Linear k R p (right k R 4 a x) =
      cochain3Linear k R p x * MulOpposite.unop a := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul b y =>
    change b * suffix3 k R p (right k R 3 a y) =
      (b * suffix3 k R p y) * MulOpposite.unop a
    rw [suffix3_right, mul_assoc]

def cochain3 (p : Cochain3 k R) : moduleObject k R 4 →ₗ[Enveloping k R] moduleObject k R 0 :=
  bimoduleMap k R (cochain3Linear k R p) (cochain3Linear_left k R p) (cochain3Linear_right k R p)

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarSuffix
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

variable [CharP k 2]

omit [CharP k 2] in

theorem suffixComparison_augmentation (p : Cochain3 k R) :
    (differential k R 0).comp (suffixComparisonMap k R p 0) = cochain3 k R p := by
  apply LinearMap.ext
  intro x
  change boundary k R 0 (suffixComparison k R p 1 x) = cochain3Linear k R p x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCasimir
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

theorem casimirMap_boundary (ξ : object k R 1) (hξ : boundary k R 0 ξ = 0) (a : R) :
    boundary k R 0 (casimirMap k R ξ a) = 0 := by
  rw [casimirMap_apply, boundary_left, hξ, map_zero]

theorem casimirInsertion_boundary_zero (ξ : object k R 1) (hξ : boundary k R 0 ξ = 0)
    (x : object k R 1) :
    boundary k R 1 (casimirInsertion k R ξ 1 x) =
      casimirMap k R ξ (boundary k R 0 x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    change boundary k R 1 (a ⊗ₜ[k] casimirMap k R ξ b) = casimirMap k R ξ (a * b)
    rw [boundary_succ_tmul, casimirMap_boundary k R ξ hξ, TensorProduct.tmul_zero,
      add_zero, casimirMap_left]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirAugmentation
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

variable [CharP k 2]

theorem twistedCasimir_augmentation (H : kˣ) :
    AbsoluteBar.boundary k R 0 (twistedCasimir q H) = 0 := by
  simp only [twistedCasimir, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [map_add, map_sum, map_sum]
  simp only [AbsoluteBar.boundary_zero_tmul k R]
  simp only [CocycleData.twist_vector q H]
  simp only [TIndex.weight, TIndex.star, Bool.false_eq_true,
    reduceIte, pow_one, pow_zero, one_smul, Bool.not_true, Bool.not_false, vector]
  change (∑ i : Letter, ((H : k) • upper q i) * lower q i) +
    (∑ i : Letter, lower q i * upper q i) = 0
  simp only [Algebra.smul_mul_assoc, ← Finset.smul_sum, upper_lower_sum, lower_upper_sum,
    smul_zero, add_zero]

end ArExplicit.T

end

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

namespace ExactProjectiveCochain

open CompleteComparison

theorem of_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveComplex (chainOfCochain K)) : ExactProjectiveCochain K where
  finite i := by
    let := hK.finite (-i)
    exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv (K.extendXIso negIndexEmbedding (i := i) (i' := -i) rfl))
  projective i := by
    let := hK.projective (-i)
    exact Module.Projective.of_equiv
      (CategoryTheory.Iso.toLinearEquiv (K.extendXIso negIndexEmbedding (i := i) (i' := -i) rfl))
  exactAt i :=
    (K.extend_exactAt_iff negIndexEmbedding (j := i) (j' := -i) rfl).mp
      ((chain_exactAt_iff (chainOfCochain K) (-i)).mpr (hK.exactAt (-i)))

end ExactProjectiveCochain

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

noncomputable def cokernelOpcyclesEquiv
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cokernel P n ≃ₗ[R] P.opcycles n :=
  ((P.opcyclesIsoSc' (n + 1) n (n - 1)
    (ChainComplex.prev ℤ n) (ChainComplex.next ℤ n)) ≪≫
      (P.sc' (n + 1) n (n - 1)).moduleCatOpcyclesIso).toLinearEquiv.symm

noncomputable def cochainCokernelEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cokernel (chainOfCochain K) n ≃ₗ[R] K.opcycles (-n) :=
  (cokernelOpcyclesEquiv (chainOfCochain K) n).trans
    (K.extendOpcyclesIso negIndexEmbedding (j := -n) (j' := n) (neg_neg n)).toLinearEquiv

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

@[simp]
theorem cokernelOpcyclesEquiv_mk (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : P.X n) :
    cokernelOpcyclesEquiv P n (Submodule.Quotient.mk x) = (P.pOpcycles n).hom x := by
  apply (cokernelOpcyclesEquiv P n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f : P.X n ⟶ ModuleCat.of R (Cokernel P n) => f.hom x)
    (show P.pOpcycles n ≫ (P.opcyclesIsoSc' (n + 1) n (n - 1)
      (ChainComplex.prev ℤ n) (ChainComplex.next ℤ n)).hom ≫
        (P.sc' (n + 1) n (n - 1)).moduleCatOpcyclesIso.hom =
          ModuleCat.ofHom (LinearMap.range (P.d (n + 1) n).hom).mkQ by
      rw [pOpcycles_opcyclesIsoSc'_hom_assoc]
      exact ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom _)
  exact h.symm

@[simp]
theorem cochainCokernelEquiv_mk (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : (chainOfCochain K).X n) :
    cochainCokernelEquiv K n (Submodule.Quotient.mk x) =
      (K.pOpcycles (-n)).hom
        ((K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).hom.hom x) := by
  change (K.extendOpcyclesIso negIndexEmbedding (neg_neg n)).hom.hom
    (cokernelOpcyclesEquiv (chainOfCochain K) n (Submodule.Quotient.mk x)) = _
  rw [cokernelOpcyclesEquiv_mk]
  exact congrArg (fun f : (chainOfCochain K).X n ⟶ K.opcycles (-n) => f.hom x)
    (pOpcycles_extendOpcyclesIso_hom K negIndexEmbedding (neg_neg n))

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeRestriction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

def Data.restrict : Data S where
  term n := (ModuleCat.restrictScalars j).obj (D.term n)
  d n := ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (D.d n))).hom
  first n := ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (D.first n))).hom
  second n := ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (D.second n))).hom
  square n := by ext x; exact DFunLike.congr_fun (D.square n) x
  first_comm n := by ext x; exact DFunLike.congr_fun (D.first_comm n) x
  second_comm n := by ext x; exact DFunLike.congr_fun (D.second_comm n) x
  comparisons_comm n := by ext x; exact DFunLike.congr_fun (D.comparisons_comm n) x

def termRestrictionEquiv (n : ℕ) :
    (ModuleCat.restrictScalars j).obj (term D n) ≃ₗ[S] term (D.restrict j) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeTail
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)
variable (g : (n : ℕ) → Q (n+3) →ₗ[R] D.term (n+2))
variable (b : (n : ℕ) → Q (n+3) →ₗ[R] D.term (n+4))

def highLift (n : ℕ) : Q (n+3) →ₗ[R] term D n :=
  (0 : Q (n+3) →ₗ[R] firstTerm D n).prod ((g n).prod (b n))

@[simp] theorem highLift_apply (n : ℕ) (x : Q (n+3)) :
    highLift D Q g b n x = ((0,0),(g n x,b n x)) := rfl

theorem highLift_comm
    (hb : ∀ n, (D.d (n+4)).comp (b (n+1)) = (b n).comp (δ (n+3)))
    (hg : ∀ n, -(D.d (n+2)).comp (g (n+1)) -
      (D.first (n+2)).comp (b (n+1)) = (g n).comp (δ (n+3)))
    (hsecondg : ∀ n, (D.second n).comp (g (n+1)) = 0)
    (hsecondb : ∀ n, (D.second (n+2)).comp (b (n+1)) = 0) (n : ℕ) :
    (d D n).comp (highLift D Q g b (n+1)) =
      (highLift D Q g b n).comp (δ (n+3)) := by
  apply LinearMap.ext
  intro x
  change d D n ((0,0),(g (n+1) x,b (n+1) x)) =
    ((0,0),(g n (δ (n+3) x),b n (δ (n+3) x)))
  rw [d_apply]
  apply Prod.ext
  · apply Prod.ext
    · simpa only [map_zero, zero_add, LinearMap.comp_apply, LinearMap.zero_apply] using DFunLike.congr_fun (hsecondg n) x
    · simpa only [map_zero, neg_zero, zero_add, LinearMap.comp_apply, LinearMap.zero_apply] using DFunLike.congr_fun (hsecondb n) x
  · exact Prod.ext (DFunLike.congr_fun (hg n) x) (DFunLike.congr_fun (hb n) x)

end ArExplicit.TwoCone

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

def homFEquiv : (F q →ₗ[C] C) ≃ rightF q where
  toFun := evaluateF q
  invFun := fromRightF q
  left_inv := fromRightF_evaluateF q
  right_inv := evaluateF_fromRightF q

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorBeta
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

theorem beta_stable_ne_zero (hq1 : 1 + q ≠ 0) :
    StableHom.classOf (A k q) (Simple q) (augmentationIdeal q) (beta q) ≠ 0 :=
  (AFrobeniusTrace k q).stable_class_ne_zero (A_trace_symmetric k q) (augmentationIdeal q)
    (augmentationIdeal_annihilates q hq1) (augmentationIdeal q).subtype Subtype.val_injective
    (fun x => x.property) (beta_ne_zero q)

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_TensorStableEnd
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] (q : k) (hq1 : 1 + q ≠ 0)

include hq1 in

theorem simple_not_projective : ¬ Module.Projective (A k q) (Simple q) := by
  intro hp
  let := hp
  let : Module.Finite (A k q) (Simple q) := Module.Finite.of_restrictScalars_finite k (A k q) _
  exact beta_stable_ne_zero q hq1 (StableHom.eq_zero_of_projective_source _)

include hq1 in
theorem stable_identity_ne_zero :
    StableHom.classOf (A k q) (Simple q) (Simple q) LinearMap.id ≠ 0 := by
  let : Module.Finite (A k q) (Simple q) := Module.Finite.of_restrictScalars_finite k (A k q) _
  intro h
  exact simple_not_projective q hq1 (StableHom.identity_eq_zero_iff.mp h)

include hq1 in

theorem simpleEnd_classOf_injective : Function.Injective
    (StableHom.classOfLinear k : (Simple q →ₗ[A k q] Simple q) →ₗ[k]
      StableHom (A k q) (Simple q) (Simple q)) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro f hf
  have hz : StableHom.classOf (A k q) (Simple q) (Simple q) f = 0 := hf
  rw [end_eq_scalar_id q hq1 f, StableHom.classOf_smul] at hz
  have hc : endScalar q f = 0 := (smul_eq_zero.mp hz).resolve_right (stable_identity_ne_zero q hq1)
  rw [end_eq_scalar_id q hq1 f, hc, zero_smul]
  exact Submodule.zero_mem _

def stableEndEquiv : StableHom (A k q) (Simple q) (Simple q) ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (StableHom.classOfLinear k)
    ⟨simpleEnd_classOf_injective q hq1, StableHom.classOf_surjective⟩).symm.trans
      (simpleEndEquiv q hq1)

@[simp]
theorem stableEndEquiv_classOf (f : Simple q →ₗ[A k q] Simple q) :
    stableEndEquiv q hq1 (StableHom.classOf (A k q) _ _ f) = endScalar q f := by
  change simpleEndEquiv q hq1 ((LinearEquiv.ofBijective (StableHom.classOfLinear k) _).symm
    ((StableHom.classOfLinear k) f)) = _
  erw [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem stableEndEquiv_identity : stableEndEquiv q hq1 StableHom.identity = 1 := by
  change stableEndEquiv q hq1 (StableHom.classOf _ _ _ LinearMap.id) = 1
  rw [stableEndEquiv_classOf]
  exact simpleGenerator_coordinate q

end ArExplicit.A

end

end OAI
end


