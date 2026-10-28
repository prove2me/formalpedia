-- Prove2me | Definitions.Def_OAIQ031A094
-- name    : OAIQ031A094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:32:17.220475+00:00
-- url     : https://prove2.me/theorems/f07bbba0-a90d-4b73-bb9f-b5cf8997177e
-- title:
--   Definitions bundle OAIQ031A094 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 10 definitions, 1 instance and 20 theorems. The definitions and types are `OAI.ArExplicit.CocycleData.simpleExtClass`, `OAI.ArExplicit.CompleteComparison.tailTermIso`, `OAI.ArExplicit.ExternalTensor.firstCubicExt`, `OAI.ArExplicit.ExternalTensor.homShort`, `OAI.ArExplicit.Resolution.exceptionalDualHomologyEquiv`, `OAI.ArExplicit.Resolution.exceptionalHomologyEquiv`, `OAI.ArExplicit.Resolution.idealDual_homology_two_iso`, `OAI.ArExplicit.Resolution.tQuotientDerivedIso`, `OAI.ArExplicit.Resolution.tQuotient_homology_iso`, `OAI.ArExplicit.Resolution.tTriangleB`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Cocycles_CocycleDetector`, `AuslanderReiten_Cocycles_CocycleExt`, `AuslanderReiten_Duality_DualResolution`, `AuslanderReiten_Duality_IdealDualComparison`, `AuslanderReiten_Duality_IdealDualComplex`, `AuslanderReiten_Duality_IdealDualHomology`, `AuslanderReiten_Ext_TExtRecurrence`, `AuslanderReiten_HomComplex_FullCochainTail`, `AuslanderReiten_HomComplex_HomCochainExt`, `AuslanderReiten_Homology_ExceptionalHomology`, `AuslanderReiten_Modules_TInducedHom`, `AuslanderReiten_Modules_TInductionHomology`, `AuslanderReiten_Modules_TInductionTriangle`, `AuslanderReiten_Tensor_ExternalTensorCubicExt`.
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A078`, `OAIQ031A080`, `OAIQ031A081` and `OAIQ031A082` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A105`, `OAIQ031A107` and `OAIQ031A108`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A080
import Definitions.Def_OAIQ031A081
import Definitions.Def_OAIQ031A082

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem tx_product : T.vector q (false, .t) * T.vector q (false, .x) = T.vector q (false, .j) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm]

theorem ty_product : T.vector q (false, .t) * T.vector q (false, .y) = q ^ 2 • T.vector q (false, .j) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm, mul_ite]

theorem xJ_product : T.vector q (false, .x) * T.vector q (true, .j) = T.vector q (true, .t) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm]

theorem yJ_product : T.vector q (false, .y) * T.vector q (true, .j) = q ^ 2 • T.vector q (true, .t) := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  simp [multiplicationCoefficient, multiplication, eq_comm, mul_ite]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleExt
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] [CharP k 2] (q : k)

def simpleExtClass : CategoryTheory.Abelian.Ext
    (ModuleBar.moduleObject k (T k q) (Resolution.Simple q) 0)
    (ModuleBar.moduleObject k (T k q) (Resolution.Simple q) 0) 3 :=
  ModuleBar.extClass3 k (T k q) (Resolution.Simple q) (p q) (p_isCocycle3 q)

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable [CharP k 2]

theorem leftEll_kernel_expand (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0)
    (a : rightE q) (ha : leftEll q r a = 0) :
    (a : C) = (a : C).coeff x • ell q (r / q) +
      (a : C).coeff z • basisVector q z + (a : C).coeff v • basisVector q v := by
  have hh : ell q r * (a : C) = 0 := congrArg Subtype.val ha
  obtain ⟨he, hu, hy⟩ := (ell_mul_eq_zero_iff q r hq hr (a : C)).mp hh
  rw [rightE_expand q a]
  simp [he, hu, hy, ell, smul_add, smul_smul, mul_comm]

theorem leftEll_exact (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0)
    (hqr : 1 + q * r ≠ 0) : Function.Exact (leftEll q r) (leftEll q (q * r)) := by
  intro a
  constructor
  · intro ha
    refine ⟨leftEllPreimage q r ((a : C).coeff x) ((a : C).coeff z) ((a : C).coeff v), ?_⟩
    apply Subtype.ext
    rw [leftEllPreimage_spec q r _ _ _ hq hr]
    have hh := leftEll_kernel_expand q (q * r) hq hqr a ha
    have hd : q * r / q = r := by field_simp
    simpa only [hd] using hh.symm
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    change ell q (q * r) * (ell q r * (b : C)) = 0
    rw [← mul_assoc]
    have hz : ell q (q * r) * ell q r = 0 := ell_successor_mul q r
    rw [hz, zero_mul]

theorem leftEll_one_kernel_expand (a : rightE q) (ha : leftEll q 1 a = 0) :
    (a : C) = (a : C).coeff y • (q • basisVector q x + basisVector q y) +
      (a : C).coeff z • basisVector q z + (a : C).coeff u • basisVector q u +
      (a : C).coeff v • basisVector q v := by
  have he := congrArg (fun b : rightE q => (b : C).coeff x) ha
  have hz := congrArg (fun b : rightE q => (b : C).coeff z) ha
  simp [ell, product] at he hz
  have hx : (a : C).coeff x = q * (a : C).coeff y := (CharTwo.add_eq_zero.mp hz).symm
  rw [rightE_expand q a]
  simp [he, hx, smul_add, smul_smul, mul_comm]

theorem leftU_exact : Function.Exact (leftU q) (leftEll q 1) := by
  intro a
  constructor
  · intro ha
    refine ⟨leftUPreimage q ((a : C).coeff u) ((a : C).coeff y)
      ((a : C).coeff z) ((a : C).coeff v), ?_⟩
    apply Subtype.ext
    rw [leftUPreimage_spec]
    conv_rhs => rw [leftEll_one_kernel_expand q a ha]
    abel
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    change ell q 1 * (basisVector q u * (b : C)) = 0
    rw [← mul_assoc, ell_one_mul_u, zero_mul]

theorem exceptional_boundary_iff (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (a : rightE q) (ha : leftEll q q a = 0) :
    (∃ b, leftEll q 1 b = a) ↔ (a : C).coeff v = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp [ell, product, CharTwo.add_self_eq_zero]
  · intro hv
    refine ⟨exceptionalBoundaryPreimage q ((a : C).coeff x) ((a : C).coeff z), ?_⟩
    apply Subtype.ext
    rw [exceptionalBoundaryPreimage_spec q _ _ hq]
    have hh := leftEll_kernel_expand q q hq hq1 a ha
    simpa [div_self hq, hv] using hh.symm

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ExceptionalHomology
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

theorem exceptionalCyclesMap_kernel (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    LinearMap.ker (exceptionalCyclesMap q hq hq1) =
      RightDualHomology.boundaries (leftEll q 1) (leftEll q q) (exceptional_differential_comp q) := by
  ext a
  constructor
  · intro ha
    have hv : (a.val : C).coeff v = 0 := by
      have hh := congrArg (simpleCoordinate q) ha
      change simpleCoordinate q ((a.val : C).coeff v • generator q) = simpleCoordinate q 0 at hh
      simpa using hh
    obtain ⟨b, hb⟩ := (exceptional_boundary_iff q hq hq1 a.val a.property).mpr hv
    exact ⟨b, Subtype.ext hb⟩
  · rintro ⟨b, hb⟩
    have he : leftEll q 1 b = a.val := congrArg Subtype.val hb
    have hv := (exceptional_boundary_iff q hq hq1 a.val a.property).mp ⟨b, he⟩
    change (a.val : C).coeff v • generator q = 0
    rw [hv, zero_smul]

def exceptionalHomologyEquiv (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ExceptionalHomology q ≃ₗ[Cᵐᵒᵖ] Simple q :=
  (Submodule.quotEquivOfEq _ _ (exceptionalCyclesMap_kernel q hq hq1).symm).trans
    ((exceptionalCyclesMap q hq hq1).quotKerEquivOfSurjective
      (exceptionalCyclesMap_surjective q hq hq1))

def exceptionalDualHomologyEquiv (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    RightDualHomology.DualHomology (k := k) (leftEll q 1) (leftEll q q)
      (exceptional_differential_comp q) ≃ₗ[C] Simple q :=
  (RightDualHomology.dualHomologyEquiv _ _ _).symm.trans
    ((RightDual.congr (exceptionalHomologyEquiv q hq hq1)).symm.trans
      (rightSimpleDualEquiv q hq1))

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualComplex
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

theorem idealDual_exact_one : Function.Exact (idealDualDifferential q 1) (idealDualDifferential q 0) := by
  change Function.Exact (RightDual.map (k := k) (leftEll q (q ^ 0))) (RightDual.map (k := k) (leftU q))
  rw [pow_zero]
  exact RightDual.map_exact (k := k) (leftU q) (leftEll q 1) (leftU_exact q)

theorem idealDual_exact_tail (hq : q ≠ 0) (h : NoPositivePowerOne q) (n : ℕ) :
    Function.Exact (idealDualDifferential q (n + 3)) (idealDualDifferential q (n + 2)) := by
  change Function.Exact (RightDual.map (k := k) (leftEll q (q ^ (n + 2))))
    (RightDual.map (k := k) (leftEll q (q ^ (n + 1))))
  have hh := RightDual.map_exact (k := k) (leftEll q (q ^ (n + 1)))
    (leftEll q (q * q ^ (n + 1)))
    (leftEll_exact q (q ^ (n + 1)) hq (h _ (by omega))
      (by simpa only [← pow_succ'] using h (n + 2) (by omega)))
  simpa only [← pow_succ'] using hh

theorem idealDual_exactAt (hq : q ≠ 0) (h : NoPositivePowerOne q) (n : ℕ) (hn : n ≠ 2) :
    (idealDualComplex q).ExactAt n := by
  match n with
  | 0 =>
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    intro z
    constructor
    · intro _
      exact idealDual_exact_zero q z
    · intro _
      change (idealDualComplex q).d 0 0 z = 0
      rw [(idealDualComplex q).shape 0 0 (by simp)]
      rfl
  | 1 =>
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((idealDualComplex q).d 2 1) ((idealDualComplex q).d 1 0)
    simpa [idealDualComplex, ChainComplex.of_d] using! idealDual_exact_one q
  | 2 => exact (hn rfl).elim
  | n + 3 =>
    rw [HomologicalComplex.exactAt_iff' _ (n + 4) (n + 3) (n + 2) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact ((idealDualComplex q).d (n + 4) (n + 3)) ((idealDualComplex q).d (n + 3) (n + 2))
    rw [show n + 4 = (n + 3) + 1 by omega, idealDualComplex_d]
    rw [show n + 3 = (n + 2) + 1 by omega, idealDualComplex_d]
    exact idealDual_exact_tail q hq h n

end ArExplicit.Resolution

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

omit [CharP k 2] in
theorem fromRightF_precompose (a : rightF q) :
    fromRightE q (leftU q a) = (fromRightF q a).comp (dU q) := by
  apply (homEEquiv q).injective
  change evaluateE q _ = evaluateE q _
  rw [evaluateE_fromRightE, evaluate_precompose_dU, evaluateF_fromRightF]

omit [CharP k 2] in
theorem fromRightE_precompose (r : k) (a : rightE q) :
    fromRightE q (leftEll q r a) = (fromRightE q a).comp (dEll q r) := by
  apply (homEEquiv q).injective
  change evaluateE q _ = evaluateE q _
  rw [evaluateE_fromRightE, evaluateE_precompose, evaluateE_fromRightE]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualHomology
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

def idealDual_homology_two_iso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (idealDualComplex q).homology 2 ≅ ModuleCat.of C (Simple q) :=
  (idealDualComplex q).homologyIsoSc' 3 2 1 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (exceptionalShortComplexIso q) ≪≫
    (exceptionalShortComplex q).moduleCatHomologyIso ≪≫
    (exceptionalDualHomologyEquiv q hq hq1).toModuleIso

end ArExplicit.Resolution

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
local notation "T" => ArExplicit.T k q

def tQuotient_homology_iso (h : NoPositivePowerOne q) :
    (TrivialInduction.quotientComplex (k := k) (complex q)).homology 0 ≅ ModuleCat.of T (Simple q) :=
  HomologicalComplex.homologyMapIso (TrivialInduction.quotientComplexIso (complex q)) 0 ≪≫
    ((complex q).sc 0).mapHomologyIso (TrivialInduction.inflate (k := k)) ≪≫
    (TrivialInduction.inflate (k := k)).mapIso (cResolution_homology_zero q h) ≪≫
    inflatedSimpleIso q

def tQuotientDerivedIso [HasDerivedCategory (ModuleCat T)]
    (h : NoPositivePowerOne q) :
    DerivedCategory.Q.obj
      ((TrivialInduction.quotientComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat) ≅
      (DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q)) :=
  concentratedNatDerivedIso _ 0 _ (tQuotient_exact q h) (tQuotient_homology_iso q h) ≪≫
    (shiftFunctorZero _ ℤ).app _

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInducedHom
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

theorem tInducedCochain_term_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 0)
    (f : (tInducedCochain q).X n ⟶ ModuleCat.of T (Simple q)) : f = 0 := by
  dsimp [tInducedCochain] at f ⊢
  by_cases hh : ∃ m : ℕ, -(m : ℤ) = n
  · obtain ⟨m, hm⟩ := hh
    have hm0 : m ≠ 0 := by intro h; subst m; simp at hm; exact hn hm.symm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    let e := (TrivialInduction.inducedComplex (k := k) (complex q)).extendXIso
      ComplexShape.embeddingDownNat hm
    apply (cancel_epi e.inv).mp
    exact (tInduced_term_hom_zero q hq1 r (e.inv ≫ f)).trans (Limits.comp_zero).symm
  · exact ((TrivialInduction.inducedComplex (k := k) (complex q)).isZero_extend_X
      ComplexShape.embeddingDownNat n (by intro m hm; exact hh ⟨m, hm⟩)).eq_of_src f 0

theorem tInduced_fullCochain_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 0)
    (a : CochainComplex.HomComplex.Cochain (tInducedCochain q)
      ((CochainComplex.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))) n) : a = 0 := by
  apply (CochainComplex.HomComplex.Cochain.toSingleEquiv (p := -n) (by omega)).injective
  rw [map_zero]
  exact tInducedCochain_term_hom_zero q hq1 (-n) (by omega) _

instance tInducedCochain_kprojective : (tInducedCochain q).IsKProjective := by
  let (n : ℕ) : Projective ((TrivialInduction.inducedComplex (k := k) (complex q)).X n) :=
    ModuleCat.projective_of_categoryTheory_projective _
  change CochainComplex.IsKProjective ((TrivialInduction.inducedComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat)
  infer_instance

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

def tTriangleB (h : NoPositivePowerOne q) : tInducedDerived q ⟶ tSimpleDerived q :=
  DerivedCategory.Q.map (tExtendedSequence q).g ≫ (tQuotientDerivedIso q h).hom

theorem tInducedDerived_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 0)
    (f : tInducedDerived q ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 :=
  derivedHom_zero_of_cochain_zero (tInducedCochain q)
    ((CochainComplex.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))) n
    (tInduced_fullCochain_zero q hq1 n hn) f

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
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD

theorem tInducedDerived_shift_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 1)
    (f : (tInducedDerived q)⟦(1 : ℤ)⟧ ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  let e := TriangleRecurrence.shiftedMapEquiv (tInducedDerived q) (tSimpleDerived q)
    1 (n - 1) n (by omega)
  obtain ⟨g, rfl⟩ := e.surjective f
  rw [tInducedDerived_hom_zero q hq1 (n - 1) (by omega) g]
  simp [e, TriangleRecurrence.shiftedMapEquiv]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullCochainTail
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)

def tailTermIso (n : ℕ) :
    (nonnegativeTail (chainOfCochain K)).X n ≅ K.X (-(n : ℤ)) :=
  K.extendXIso negIndexEmbedding (by change -(-(n : ℤ))=(n : ℤ); omega)

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

abbrev homShort (n : ℕ) := (homCochain k R P.complex Y).sc' (n-1) n (n+1)

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

include hp in
omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))] in
theorem firstComparison_comm (n : ℕ) :
    firstComparison k A B P Q p (n+1) ≫ (projectiveResolution k A B P Q).complex.d (n+1) n =
      (projectiveResolution k A B P Q).complex.d (n+4) (n+3) ≫ firstComparison k A B P Q p n :=
  ModuleCat.hom_ext (firstCubic_chain k A B P.complex Q.complex p hp n)

def firstCubicExt : Ext (moduleObject k A B X Y) (moduleObject k A B X Y) 3 :=
  ResolutionProducts.endExt (projectiveResolution k A B P Q)
    (ResolutionProducts.natCubicCocycle (k := k) (projectiveResolution k A B P Q)
      (firstComparison k A B P Q p) (firstComparison_comm k A B P Q p hp))

end ArExplicit.ExternalTensor

end

end OAI
end


