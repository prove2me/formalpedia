-- Prove2me | Definitions.Def_OAIQ031A106
-- name    : OAIQ031A106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:40:39.248071+00:00
-- url     : https://prove2.me/theorems/6651c6fa-e840-462a-b41b-ce25032c6a13
-- title:
--   Definitions bundle OAIQ031A106 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 7 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.fullPositiveExtEquiv`, `OAI.ArExplicit.ModuleBar.cubicMap`, `OAI.ArExplicit.ModuleBar.nativeCubicMap`, `OAI.ArExplicit.ModuleBar.suffixComparisonMap`, `OAI.ArExplicit.Resolution.idealDualEquiv`, `OAI.ArExplicit.Resolution.rawIdealDualEquivE`, `OAI.ArExplicit.Resolution.rawIdealDualEquivF`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCubic.lean), [`AuslanderReiten_Bar_ModuleBarNative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNative.lean), [`AuslanderReiten_Bar_ModuleBarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarSuffix.lean), [`AuslanderReiten_Bar_TBarHomotopies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TBarHomotopies.lean), [`AuslanderReiten_Cocycles_ReversedCocycleMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/ReversedCocycleMap.lean), [`AuslanderReiten_Coordinates_TensorHighLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorHighLift.lean), [`AuslanderReiten_Duality_IdealDualComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/IdealDualComparison.lean), [`AuslanderReiten_HomComplex_FiniteFullHomZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FiniteFullHomZero.lean), [`AuslanderReiten_HomComplex_PositiveFullHomExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/PositiveFullHomExt.lean), [`AuslanderReiten_Stable_SourceStableCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/SourceStableCoordinates.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A081`, `OAIQ031A092` and `OAIQ031A093` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A118`, `OAIQ031A119`, `OAIQ031A120`, `OAIQ031A121`, `OAIQ031A122` and `OAIQ031A126`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A081
import Definitions.Def_OAIQ031A092
import Definitions.Def_OAIQ031A093

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarSuffix
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem suffixComparison_left (p : AbsoluteBar.Cochain3 k R) (n : ℕ) (a : R)
    (x : object k R M (n + 4)) :
    suffixComparison k R M p (n + 1) (left k R M (n + 4) a x) =
      left k R M (n + 1) a (suffixComparison k R M p (n + 1) x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => rfl

def suffixComparisonMap (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    moduleObject k R M (n + 4) →ₗ[R] moduleObject k R M (n + 1) where
  toAddHom := (suffixComparison k R M p (n + 1)).toAddHom
  map_smul' a x := suffixComparison_left k R M p n a x

variable [CharP k 2]

theorem suffixComparison_boundary_zero (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    (boundary k R M 0).comp (suffixComparison k R M p 1) =
      (suffixComparison k R M p 0).comp (boundary k R M 3) := by
  ext a b c d e
  change a • (p b c d • e) = suffix3 k R M p
    (boundary k R M 3 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))))
  have h := congrArg (fun x : R => x • e) (hp a b c d)
  simp only [add_smul, zero_smul, mul_smul] at h
  simp only [boundary_succ_tmul k R M 2, boundary_succ_tmul k R M 1,
    boundary_succ_tmul k R M 0, boundary_zero_tmul k R M,
    left_tmul k R M 2, left_tmul k R M 1, left_tmul k R M 0,
    TensorProduct.tmul_add, map_add, suffix3_tmul k R M p]
  have h' : a • (p b c d • e) +
      (p (a * b) c d • e + (p a (b * c) d • e +
        (p a b (c * d) • e + p a b c • (d • e)))) = 0 := by
    simpa only [add_assoc] using h
  have hz := double_zero_p1 k (a • (p b c d • e))
  have hh := congrArg (fun x : M => a • (p b c d • e) + x) h'
  simpa only [← add_assoc, hz, zero_add, add_zero] using hh.symm

theorem suffixComparison_boundary (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) (n : ℕ)
    (x : object k R M (n + 4)) :
    boundary k R M n (suffixComparison k R M p (n + 1) x) =
      suffixComparison k R M p n (boundary k R M (n + 3) x) := by
  induction n with
  | zero => exact LinearMap.congr_fun (suffixComparison_boundary_zero k R M p hp) x
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      change boundary k R M (n + 1) (a ⊗ₜ[k] suffixComparison k R M p (n + 1) x) =
        suffixComparison k R M p (n + 1) (boundary k R M (n + 4) (a ⊗ₜ[k] x))
      rw [boundary_succ_tmul k R M n, boundary_succ_tmul k R M (n + 3), map_add,
        suffixComparison_left k R M p n, suffixComparison_succ_tmul, ih]

end ArExplicit.ModuleBar

end

end OAI
end

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

def cubicMap (n : ℕ) : (resolution k R M).complex.X (n+3) ⟶ (resolution k R M).complex.X n :=
  ModuleCat.ofHom (X := moduleObject k R M (n+4)) (Y := moduleObject k R M (n+1))
    (suffixComparisonMap k R M p n)

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

def nativeCubicMap (n : ℕ) : (nativeResolution k R M).complex.X (n+3) ⟶
    (nativeResolution k R M).complex.X n := cubicMap k R M p n

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TBarHomotopies
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

theorem barDb_cycle : (Q₀).d 1 0 ≫ barDb q H = 0 := by
  have hs : (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0).comp
      (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 1) = 0 := by
    apply LinearMap.ext
    intro x
    exact AbsoluteBar.boundary_squared k R 0 x
  rw [AbsoluteBar.twistedComplex_d]
  apply ModuleCat.hom_ext
  change ((B q H 0).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0)).comp
    (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 1) = 0
  rw [LinearMap.comp_assoc, hs, LinearMap.comp_zero]

theorem barB_chain (n : ℕ) :
    barB q H (n+1) ≫ (P₀).d (n+2) (n+1) = (Q₀).d (n+1) n ≫ barB q H n := by
  simp only [AbsoluteBar.complex_d, AbsoluteBar.twistedComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (B_differential q H (n+1)) x
  exact add_right_cancel (hh.trans
    (SparseParity.module_add_self_eq_zero (k := k) (B q H (n+1)
      (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n+1) x))).symm)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_SourceStableCoordinates
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

theorem sourceCocycleMap_mk [CharP k 2] (x : Cocycle K L n)
    (z : (chainOfCochain K).X n) :
    sourceCocycleMap x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((sourceCocycleComponent x).hom z) := by
  change shiftedCokernelEquiv L 0 0 rfl
    (cokernelMap (cocycleComparisonMap (x.leftShift (-n) 0 (by omega))) 0
      ((shiftedCokernelEquiv K (-n) n rfl).symm (Submodule.Quotient.mk z))) = _
  rw [shiftedCokernelEquiv_symm_mk]
  change shiftedCokernelEquiv L 0 0 rfl
    (Submodule.Quotient.mk
      (((cocycleComparisonMap (x.leftShift (-n) 0 (by omega))).f 0).hom
        ((shiftedCokernelComponent K (-n) n rfl).inv.hom z))) = _
  rw [shiftedCokernelEquiv_mk]
  congr 1
  unfold cocycleComparisonMap
  rw [extendMap_f _ negIndexEmbedding (show negIndexEmbedding.f 0 = 0 from rfl)]
  rw [cocycleHom_component]
  simp only [Cocycle.leftShift_coe]
  rw [Cochain.leftShift_v _ (-n) 0 (by omega) 0 (0 + 0) rfl (-n) (by omega)]
  rw [ResolutionProducts.intUnit_smul_charTwo (k := k)]
  have hh : (shiftedCokernelComponent K (-n) n rfl).inv ≫
      ((K⟦-n⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom ≫
      (K.shiftFunctorObjXIso (-n) 0 (-n) (by omega)).hom ≫
      x.val.v (-n) 0 (by omega) ≫
      ((L⟦(0 : ℤ)⟧).extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).inv ≫
      (shiftedCokernelComponent L 0 0 rfl).hom = sourceCocycleComponent x := by
    dsimp only [shiftedCokernelComponent, sourceCocycleComponent]
    erw [Iso.trans_inv, Iso.trans_inv, Iso.trans_hom, Iso.trans_hom]
    simp only [Iso.symm_inv, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      CochainComplex.shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom]
    erw [Category.id_comp]
    all_goals (simp; try erw [Iso.inv_hom_id_assoc])
  exact congrArg (fun f : (chainOfCochain K).X n ⟶ (chainOfCochain L).X 0 => f.hom z) hh

end ArExplicit.CompleteComparison

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

theorem reversedComponent_comm (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    reversedComponent x.val (a+1) (b+1) (by omega) ≫ (chainOfCochain L).d (b+1) b =
      (chainOfCochain K).d (a+1) a ≫ reversedComponent x.val a b hab := by
  have hx := congrArg (fun z : Cochain K L (n+1) => z.v (-(a+1)) (-b) (by omega))
    (show δ n (n+1) x.val=0 by simp)
  rw [δ_v _ _ rfl _ _ _ (by omega) (-(b+1)) (-a) (by omega) (by omega),
    ResolutionProducts.intUnit_smul_charTwo (k := k), Cochain.zero_v] at hx
  have he : x.val.v (-(a+1)) (-(b+1)) (by omega) ≫ L.d (-(b+1)) (-b) =
      K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega) := by
    have hh : (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) +
        (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) = 0 := by
      rw [← two_smul k, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
    exact (eq_neg_of_add_eq_zero_left hx).trans (eq_neg_iff_add_eq_zero.mpr hh).symm
  rw [L.extend_d_eq negIndexEmbedding (neg_neg (b+1)) (neg_neg b),
    K.extend_d_eq negIndexEmbedding (neg_neg (a+1)) (neg_neg a)]
  simp only [reversedComponent, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun z =>
    (K.extendXIso negIndexEmbedding (neg_neg (a+1))).hom ≫ z ≫
      (L.extendXIso negIndexEmbedding (neg_neg b)).inv) he

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorHighLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)
local notation "D" => productTwoConeData q

theorem tensorHighB_chain (n : ℕ) :
    ((D).d (n+4)).comp (tensorHighB q H (n+1)) =
      (tensorHighB q H n).comp ((productTwistedTotal q H).d (n+4) (n+3)).hom := by
  change ((ExternalTensor.complex k Te Te P₀ P₀).d (n+5) (n+4)).hom.comp
      (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+4) (n+5)
        (barB q H (n+4)) (barDb q H)) =
    (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+4)
      (barB q H (n+3)) (barDb q H)).comp
      ((productTwistedTotal q H).d (n+4) (n+3)).hom
  rw [ExternalTensor.bottomMap_d_target,
    ExternalTensor.bottomMap_d_source k Te Te (hg := barDb_cycle q H), barB_chain]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualComparison
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def rawIdealDualEquivF : RightDual k C (F q →ₗ[C] C) ≃ₗ[C] RightDual k C (rightF q) :=
  (RightDual.congr (homFRightLinearEquiv q)).symm

def rawIdealDualEquivE : RightDual k C (E q →ₗ[C] C) ≃ₗ[C] RightDual k C (rightE q) :=
  (RightDual.congr (homERightLinearEquiv q)).symm

def idealDualEquiv : (n : ℕ) →
    (DualTensor.dualHomComplex (k := k) (complex q)).X n ≃ₗ[C] (idealDualComplex q).X n
  | 0 => rawIdealDualEquivF q
  | _ + 1 => rawIdealDualEquivE q

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FiniteFullHomZero
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
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]

namespace CompleteComparison
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

include k in
theorem sourceCocycleMap_ofHom (f : K ⟶ L) :
    sourceCocycleMap (Cocycle.ofHom f) = cokernelMap (extendMap f negIndexEmbedding) 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range ((chainOfCochain K).d 1 0).hom).mkQ_surjective z
  change sourceCocycleMap (Cocycle.ofHom f) (Submodule.Quotient.mk x) = _
  rw [sourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk ((sourceCocycleComponent (Cocycle.ofHom f)).hom x) =
    Submodule.Quotient.mk (((extendMap f negIndexEmbedding).f 0).hom x)
  congr 2
  unfold sourceCocycleComponent
  rw [extendMap_f f negIndexEmbedding (show negIndexEmbedding.f 0 = 0 from rfl)]
  rfl

end CompleteComparison

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_PositiveFullHomExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

def fullPositiveExtEquiv (n : ℕ) :
    CohomologyClass K L ((n+1 : ℕ) : ℤ) ≃ₗ[k]
      Abelian.Ext (ModuleCat.of R (Cokernel (chainOfCochain K) 0))
        (ModuleCat.of R (Cokernel (chainOfCochain L) 0)) (n+1) :=
  (fullHomSourceStableLinearEquiv (k := k) K L ((n+1 : ℕ) : ℤ) hK hL).trans
    (positiveExtStableEquiv (k := k) hK
      (ModuleCat.of R (Cokernel (chainOfCochain L) 0)) n).symm

end ArExplicit.CompleteComparison

end

end OAI
end


