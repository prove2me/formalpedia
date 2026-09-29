-- Prove2me | solution 1 for AutomorphicForm.exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/64b9fca6-c80b-5d58-ba22-3d8144a9047a

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped nonZeroDivisors

section Units

variable {K : Type} [Field K] [NumberField K]

private noncomputable def finShift (y : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K :=
  ((0 : InfiniteAdeleRing K), y)
private theorem finShift_fst (y : FiniteAdeleRing (𝓞 K) K) : (finShift y).1 = 0 := rfl
private theorem finShift_snd (y : FiniteAdeleRing (𝓞 K) K) : (finShift y).2 = y := rfl

private theorem algebraMap_mul_mem_integralFiniteAdeles (a : 𝓞 K) {r : FiniteAdeleRing (𝓞 K) K}
    (hr : r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  intro v
  rw [NumberField.AdelicLevel.coe_mul_apply]
  exact mul_mem (NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v a) (hr v)

private theorem exists_algebraMap_mul_mem (y : FiniteAdeleRing (𝓞 K) K) :
    ∃ b : 𝓞 K, b ≠ 0 ∧
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  obtain ⟨b, hb, hby⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles (R := 𝓞 K) (K := K) y
  exact ⟨b, hb, fun v => hby v⟩

private theorem exists_algebraMap_mul_mem_of_finset (S : Finset (FiniteAdeleRing (𝓞 K) K)) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ ∀ y ∈ S,
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert z S _ ih =>
    obtain ⟨b₁, hb₁, h₁⟩ := ih
    obtain ⟨b₂, hb₂, h₂⟩ := exists_algebraMap_mul_mem (K := K) z
    refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hyS
    · rw [map_mul, mul_assoc]
      exact algebraMap_mul_mem_integralFiniteAdeles b₁ h₂
    · rw [map_mul, mul_comm (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b₁), mul_assoc]
      exact algebraMap_mul_mem_integralFiniteAdeles b₂ (h₁ y hyS)

private theorem algebraMap_mul_mem_idealBall {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) {n : 𝓞 K} (hn : n ∈ N)
    {z : FiniteAdeleRing (𝓞 K) K} (hz : z ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) n * z ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N := by
  classical
  intro v
  have hnv : Valued.v ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) n) v) = v.intValuation n :=
    NumberField.AdelicLevel.valued_algebraMap v n
  rw [NumberField.AdelicLevel.coe_mul_apply, Valuation.map_mul, hnv]
  have hz1 : Valued.v (z v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v)
  refine (mul_le_of_le_one_right' hz1).trans ?_
  rw [NumberField.AdelicLevel.idealBound_of_ne_bot hN]
  by_cases hn0 : n = 0
  · subst hn0
    simp
  rw [HeightOneSpectrum.intValuation_if_neg v hn0, WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]

  have hspan := Associates.mk_le_mk_iff_dvd.2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem N).2 hn))
  have hne : Associates.mk (Ideal.span {n} : Ideal (𝓞 K)) ≠ 0 :=
    Associates.mk_ne_zero.2 (Ideal.span_singleton_eq_bot.not.2 hn0)
  exact Associates.count_le_count_of_le hne (HeightOneSpectrum.associates_irreducible v) hspan

private theorem glFin_unipotentGL2_finShift (y : FiniteAdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 (finShift y)) = unipotentGL2 y := by
  ext i j
  rw [NumberField.AdelicLevel.glFin_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem glArch_unipotentGL2_finShift (y : FiniteAdeleRing (𝓞 K) K) :
    glArch (𝓞 K) K (unipotentGL2 (finShift y)) = 1 := by
  ext i j
  rw [NumberField.AdelicLevel.glArch_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem unipotentGL2_coe_eq (y : FiniteAdeleRing (𝓞 K) K) :
    (unipotentGL2 y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
      = 1 + y • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : FiniteAdeleRing (𝓞 K) K) := by
  rw [unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single, Matrix.one_apply]

private theorem conj_unipotentGL2_coe (k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (y : FiniteAdeleRing (𝓞 K) K) :
    ((k⁻¹ * unipotentGL2 y * k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
      = 1 + y • (((k⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
          * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : FiniteAdeleRing (𝓞 K) K)
          * (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe_eq, mul_add, add_mul, mul_one, Units.inv_mul,
    Matrix.mul_smul, Matrix.smul_mul]

private theorem single_entry_mem (i j : Fin 2) :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : FiniteAdeleRing (𝓞 K) K) i j
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, NumberField.AdelicLevel.one_mem_integralFiniteAdeles,
      NumberField.AdelicLevel.zero_mem_integralFiniteAdeles]

private theorem mul_entry_mem {A C : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hA : ∀ i j, A i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hC : ∀ i j, C i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K) (i j : Fin 2) :
    (A * C) i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact NumberField.AdelicLevel.add_mem_integralFiniteAdeles
    (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hA i 0) (hC 0 j))
    (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hA i 1) (hC 1 j))

private theorem exists_conjugation_ideal_ball (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
        ∀ r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K,
          g⁻¹ * unipotentGL2 (finShift (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r)) * g
              ∈ finiteAdelicGL2Subgroup K ∧
            (∀ i j, ((glFin (𝓞 K) K
                (g⁻¹ * unipotentGL2 (finShift (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r)) * g) :
                  Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) ∧
            (∀ i j, ((((glFin (𝓞 K) K
                (g⁻¹ * unipotentGL2 (finShift (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r)) * g))⁻¹ :
                  GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
                  Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) := by
  classical

  obtain ⟨n₀, hn₀N, hn₀⟩ := (Submodule.ne_bot_iff N).1 hN

  set S : Finset (FiniteAdeleRing (𝓞 K) K) := T.biUnion fun x =>
    (Finset.univ : Finset (Fin 2 × Fin 2)).image
        (fun p => (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p.1 p.2) ∪
      (Finset.univ : Finset (Fin 2 × Fin 2)).image
        (fun p => (((glFin (𝓞 K) K x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p.1 p.2)
  obtain ⟨b, hb, hbS⟩ := exists_algebraMap_mul_mem_of_finset (K := K) S
  refine ⟨n₀ * (b * b), mul_ne_zero hn₀ (mul_ne_zero hb hb), ?_⟩
  intro g hg r hr
  obtain ⟨x, hxT, s, hs, rfl⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_image, exists_prop] using hg

  have hsInt := NumberField.AdelicLevel.mem_finiteIntegralGL2_iff.1 (mem_centreCutSiegelSet_iff.1 hs).1
  have hxcl : ∀ i j,
      algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b * (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) _) i j
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K ∧
        algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) b *
            (((glFin (𝓞 K) K x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) i j
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    constructor
    · exact hbS _ (Finset.mem_biUnion.2 ⟨x, hxT, Finset.mem_union.2 (Or.inl
        (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩)
    · exact hbS _ (Finset.mem_biUnion.2 ⟨x, hxT, Finset.mem_union.2 (Or.inr
        (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩)

  set kx : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) := glFin (𝓞 K) K x
  set ks : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) := glFin (𝓞 K) K s
  set E : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) := Matrix.single (0 : Fin 2) (1 : Fin 2) 1 with hE
  set C : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    ((ks⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) * E * (ks : Matrix (Fin 2) (Fin 2) _)
    with hC
  have hEint : ∀ i j, E i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    rw [hE]
    exact single_entry_mem i j
  have hCint : ∀ i j, C i j ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    rw [hC]
    exact mul_entry_mem (mul_entry_mem hsInt.2 hEint) hsInt.1 i j
  have hgfin : glFin (𝓞 K) K (s * x) = ks * kx := map_mul _ _ _
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    (((ks * kx)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) * E *
      ((ks * kx : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) with hM
  have hMeq : M = ((kx⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) * C *
      (kx : Matrix (Fin 2) (Fin 2) _) := by
    simp only [hM, hC, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

  have hMcl : ∀ i j, algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (b * b) * M i j
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    intro i j
    have hterm : ∀ l : Fin 2, algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (b * b) *
        ((((kx⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) * C :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i l *
          (kx : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) l j)
        ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
      intro l
      have h := NumberField.AdelicLevel.mul_mem_integralFiniteAdeles
        (NumberField.AdelicLevel.add_mem_integralFiniteAdeles
          (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hxcl i 0).2 (hCint 0 l))
          (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hxcl i 1).2 (hCint 1 l)))
        (hxcl l j).1
      convert h using 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, map_mul]
      ring
    rw [hMeq, Matrix.mul_apply, Fin.sum_univ_two, mul_add]
    exact NumberField.AdelicLevel.add_mem_integralFiniteAdeles (hterm 0) (hterm 1)

  have hball : ∀ r' ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K, ∀ i j,
      ((algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) (n₀ * (b * b)) * r') • M) i j
        ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K N := by
    intro r' hr' i j
    have h := algebraMap_mul_mem_idealBall hN hn₀N
      (NumberField.AdelicLevel.mul_mem_integralFiniteAdeles (hMcl i j) hr')
    convert h using 1
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    ring

  have hnegr : -r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    simpa using NumberField.AdelicLevel.sub_mem_integralFiniteAdeles
      NumberField.AdelicLevel.zero_mem_integralFiniteAdeles hr
  have hinv : ∀ y : FiniteAdeleRing (𝓞 K) K,
      ((ks * kx)⁻¹ * unipotentGL2 y * (ks * kx))⁻¹ = (ks * kx)⁻¹ * unipotentGL2 (-y) * (ks * kx) := by
    intro y
    have h1 : unipotentGL2 y * unipotentGL2 (-y) = 1 := by
      rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
    have h2 : ((ks * kx)⁻¹ * unipotentGL2 y * (ks * kx)) * ((ks * kx)⁻¹ * unipotentGL2 (-y) * (ks * kx))
        = (ks * kx)⁻¹ * (unipotentGL2 y * unipotentGL2 (-y)) * (ks * kx) := by
      group
    rw [h1, mul_one, inv_mul_cancel] at h2
    exact inv_eq_of_mul_eq_one_right h2
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_unipotentGL2_finShift, mul_one,
      inv_mul_cancel]
  ·
    intro i j
    rw [map_mul, map_mul, map_inv, glFin_unipotentGL2_finShift, hgfin, conj_unipotentGL2_coe, add_sub_cancel_left]
    exact hball r hr i j
  ·
    intro i j
    rw [map_mul, map_mul, map_inv, glFin_unipotentGL2_finShift, hgfin, hinv, conj_unipotentGL2_coe, ← mul_neg,
      add_sub_cancel_left]
    exact hball (-r) hnegr i j

private theorem whittakerCoefficient_eq_zero_of_shift
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g : AdelicGL2 (𝓞 K) K)
    (y : FiniteAdeleRing (𝓞 K) K) (hy : y ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (hshift : ∀ x : AdeleRing (𝓞 K) K,
      f (unipotentGL2 (finShift y + x) * g) = f (unipotentGL2 x * g))
    (hψ : ψ (algebraMap K (AdeleRing (𝓞 K) K) α * finShift y) ≠ 1) :
    whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ f α g = 0 := by
  classical

  have hbox : ∀ x : AdeleRing (𝓞 K) K, finShift y + x ∈ adelicBox K ↔ x ∈ adelicBox K := by
    intro x
    have e1 : (finShift y + x).1 = x.1 := zero_add x.1
    have e2 : (finShift y + x).2 = y + x.2 := rfl
    simp only [adelicBox, Set.mem_setOf_eq, e1, e2]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 := NumberField.AdelicLevel.sub_mem_integralFiniteAdeles h2 hy
      rwa [add_sub_cancel_left] at h3
    · rintro ⟨h1, h2⟩
      exact ⟨h1, NumberField.AdelicLevel.add_mem_integralFiniteAdeles hy h2⟩
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  haveI : (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K).IsAddHaarMeasure :=
    NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  set G : AdeleRing (𝓞 K) K → ℂ :=
    fun x => f (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) with hG
  set c : ℂ := ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * finShift y)) with hc
  have hc1 : c ≠ 1 := by
    rw [hc, AddChar.map_neg_eq_inv]
    exact inv_ne_one.mpr hψ
  have hGshift : ∀ x, G (finShift y + x) = c * G x := by
    intro x
    simp only [hG, hc]
    rw [hshift x, mul_add, neg_add, AddChar.map_add_eq_mul]
    ring
  have hind : ∀ x, (adelicBox K).indicator G (finShift y + x) = c * (adelicBox K).indicator G x := by
    intro x
    by_cases hx : x ∈ adelicBox K
    · rw [Set.indicator_of_mem ((hbox x).2 hx), Set.indicator_of_mem hx, hGshift]
    · rw [Set.indicator_of_notMem (fun h => hx ((hbox x).1 h)), Set.indicator_of_notMem hx, mul_zero]
  have hI : (∫ x, (adelicBox K).indicator G x ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K)) = 0 := by
    have h1 := MeasureTheory.integral_add_left_eq_self (μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K)
      ((adelicBox K).indicator G) (finShift y)
    simp_rw [hind] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (c - 1) * (∫ x, (adelicBox K).indicator G x ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K)) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) hc1
    · exact h
  show (∫ x, G x ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) (adelicBox K))) = 0
  rw [ProbabilityTheory.cond, MeasureTheory.integral_smul_measure,
    ← MeasureTheory.integral_indicator (measurableSet_adelicBox K), hI, smul_zero]

private theorem psiLocal_level_facts (v : HeightOneSpectrum (𝓞 K)) :
    (∀ x : v.adicCompletion K,
        Valued.v x ≤ WithZero.exp (LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)) →
          StandardAddChar.psiLocal K v x = 1) ∧
      ∃ x : v.adicCompletion K,
        Valued.v x ≤ WithZero.exp (LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v) + 1) ∧
          StandardAddChar.psiLocal K v x ≠ 1 :=
  LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v (StandardAddChar.psiLocal K v)
    ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v x
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by simpa using hx))⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)

private theorem valuation_le_exp_neg_addCharLevel (v : HeightOneSpectrum (𝓞 K)) {D : 𝓞 K}
    (hD : D ∈ differentIdeal ℤ (𝓞 K)) (hD0 : D ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K D)
      ≤ WithZero.exp (-LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)) := by
  classical
  have hJ : (Ideal.span {D} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hD0
  have hle : ((Ideal.span {D} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hD)
  have hmono := FractionalIdeal.count_mono (K := K) (v := v) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) hle
  rw [← LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K v,
    FractionalIdeal.count_coe (K := K) (v := v) (show (Ideal.span {D} : Ideal (𝓞 K)) ≠ 0 from hJ)] at hmono
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hD0, WithZero.exp_le_exp]
  exact neg_le_neg hmono

open NumberField.StandardAddChar in

private theorem exists_unit_fractionalIdeal_stdAddChar_ne_one (a : 𝓞 K) (ha : a ≠ 0) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ α : K, α ∉ (I : FractionalIdeal (𝓞 K)⁰ K) →
      ∃ r ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 K) K,
        StandardAddChar.stdAddChar K
          (algebraMap K (AdeleRing (𝓞 K) K) α * finShift (algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a * r)) ≠ 1 := by
  classical

  have h𝔇 : differentIdeal ℤ (𝓞 K) ≠ ⊥ := by
    intro h
    have hn := NumberField.absNorm_differentIdeal K (𝓞 K)
    rw [h, Ideal.absNorm_bot] at hn
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K) hn.symm
  obtain ⟨D, hD𝔇, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔇
  set c : K := algebraMap (𝓞 K) K (a * D) with hc
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hc0 : c ≠ 0 := by
    rw [hc, map_ne_zero_iff _ hinj]
    exact mul_ne_zero ha hD0
  have hI0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ c⁻¹ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hc0)
  refine ⟨Units.mk0 _ hI0, fun α hα => ?_⟩

  have hnot : α * c ∉ (algebraMap (𝓞 K) K).range := by
    rintro ⟨z, hz⟩
    refine hα ?_
    rw [Units.val_mk0, FractionalIdeal.mem_spanSingleton]
    exact ⟨z, by rw [Algebra.smul_def, hz, mul_assoc, mul_inv_cancel₀ hc0, mul_one]⟩

  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 K), 1 < v.valuation K (α * c) := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hnot (HeightOneSpectrum.mem_integers_of_valuation_le_one K (α * c) h)

  set n : ℤ := LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v) with hn
  obtain ⟨-, x₀, hx₀v, hx₀⟩ := psiLocal_level_facts (K := K) v
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hαa0 : v.valuation K (α * algebraMap (𝓞 K) K a) ≠ 0 := by
    refine (Valuation.ne_zero_iff _).mpr (mul_ne_zero ?_ ha0)
    rintro rfl
    rw [zero_mul, map_zero] at hv
    exact (not_lt.mpr zero_le') hv
  have hαa : WithZero.exp (n + 1) ≤ v.valuation K (α * algebraMap (𝓞 K) K a) := by
    have hDv := valuation_le_exp_neg_addCharLevel (K := K) v hD𝔇 hD0
    have h1 : 1 < v.valuation K (α * algebraMap (𝓞 K) K a) * WithZero.exp (-n) := by
      refine lt_of_lt_of_le ?_ (mul_le_mul_right hDv _)
      rw [← map_mul, mul_assoc, ← map_mul]
      exact hv
    rw [← WithZero.exp_log hαa0] at h1 ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]
    omega

  set X : FiniteAdeleRing (𝓞 K) K := algebraMap K (FiniteAdeleRing (𝓞 K) K) α with hX
  set A : FiniteAdeleRing (𝓞 K) K := algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) a with hA
  have hAK : A = algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a) := rfl
  have hPval : Valued.v (X v * A v) = v.valuation K (α * algebraMap (𝓞 K) K a) := by
    rw [map_mul, map_mul, hX, hAK, FiniteAdeleRing.algebraMap_apply, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hP0 : X v * A v ≠ 0 := by
    intro h0
    apply hαa0
    rw [← hPval, h0, map_zero]

  set y₀ : v.adicCompletion K := (X v * A v)⁻¹ * x₀ with hy₀
  have hy₀int : y₀ ∈ v.adicCompletionIntegers K := by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
    rw [hy₀, map_mul, map_inv₀, hPval]
    calc (v.valuation K (α * algebraMap (𝓞 K) K a))⁻¹ * Valued.v x₀
        ≤ (v.valuation K (α * algebraMap (𝓞 K) K a))⁻¹ * v.valuation K (α * algebraMap (𝓞 K) K a) :=
          mul_le_mul_right (hx₀v.trans hαa) _
      _ = 1 := inv_mul_cancel₀ hαa0
  refine ⟨finAdeleSingleAt K v y₀, fun w => ?_, ?_⟩
  · by_cases hw : w = v
    · rw [hw, finAdeleSingleAt_apply_self]
      exact hy₀int
    · rw [finAdeleSingleAt_apply_of_ne K v y₀ hw]
      exact zero_mem _
  ·
    have hfin : X * (A * finAdeleSingleAt K v y₀) = finAdeleSingleAt K v x₀ := by
      refine FiniteAdeleRing.ext K fun w => ?_
      rw [NumberField.AdelicLevel.coe_mul_apply, NumberField.AdelicLevel.coe_mul_apply]
      by_cases hw : w = v
      · rw [hw, finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self, hy₀,
          show X v * (A v * ((X v * A v)⁻¹ * x₀)) = X v * A v * (X v * A v)⁻¹ * x₀ by ring,
          mul_inv_cancel₀ hP0, one_mul]
      · rw [finAdeleSingleAt_apply_of_ne K v y₀ hw, finAdeleSingleAt_apply_of_ne K v x₀ hw, mul_zero, mul_zero]
    have hadele : algebraMap K (AdeleRing (𝓞 K) K) α * finShift (A * finAdeleSingleAt K v y₀) =
        finShift (finAdeleSingleAt K v x₀) := by
      refine Prod.ext ?_ ?_
      · show (algebraMap K (AdeleRing (𝓞 K) K) α).1 * 0 = 0
        exact mul_zero _
      · show algebraMap K (FiniteAdeleRing (𝓞 K) K) α * (A * finAdeleSingleAt K v y₀) = finAdeleSingleAt K v x₀
        exact hfin
    rw [hadele]
    show StandardAddChar.stdAddChar K ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x₀) ≠ 1
    rw [← StandardAddChar.psiLocal_apply]
    exact hx₀

private theorem shift_of_forall_mul_eq {f : AdelicGL2 (𝓞 K) K → ℂ} {g : AdelicGL2 (𝓞 K) K} {t : AdeleRing (𝓞 K) K}
    (hf : ∀ h : AdelicGL2 (𝓞 K) K, f (h * (g⁻¹ * unipotentGL2 t * g)) = f h) (x : AdeleRing (𝓞 K) K) :
    f (unipotentGL2 (t + x) * g) = f (unipotentGL2 x * g) := by
  have h1 : unipotentGL2 (t + x) * g = unipotentGL2 x * g * (g⁻¹ * unipotentGL2 t * g) := by
    rw [add_comm, unipotentGL2_add]
    group
  rw [h1]
  exact hf _

end Units

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ (f : AdelicGL2 (𝓞 K) K → ℂ),
        (∀ (h : AdelicGL2 (𝓞 K) K), ∀ u' ∈ finiteAdelicGL2Subgroup K,
          (∀ i j, ((glFin (𝓞 K) K u' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
            idealBall (𝓞 K) K N) →
          (∀ i j, ((((glFin (𝓞 K) K u')⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          f (h * u') = f h) →
        ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
          ∀ α : K, α ∉ (I : FractionalIdeal (𝓞 K)⁰ K) →
            whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) f α g = 0 := by
  obtain ⟨a, ha, hA⟩ := exists_conjugation_ideal_ball c u d₁ d₂ T N hN
  obtain ⟨I, hI⟩ := exists_unit_fractionalIdeal_stdAddChar_ne_one a ha
  refine ⟨I, ?_⟩
  intro f hf g hg α hα
  obtain ⟨r, hr, hψ⟩ := hI α hα
  obtain ⟨hfin, hK, hK'⟩ := hA g hg r hr
  exact whittakerCoefficient_eq_zero_of_shift _ _ _ _ f α g _ (algebraMap_mul_mem_integralFiniteAdeles a hr)
    (fun x => shift_of_forall_mul_eq (fun h => hf h _ hfin hK hK') x) hψ

end S_AutomorphicForm_exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq (solution)
