-- Prove2me | solution 1 for AutomorphicForm.exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c94a2334-0ad8-565c-a3f1-51cdd22daaa0

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Int
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
import Theorems.Thm_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero
import Theorems.Thm_AutomorphicForm_eq_zero_of_mem_isotypicCuspSubmodule_of_forall_det_eq_one_invariant
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_mem_localLevelOne_smul_eq_of_smooth_of_det_one_invariant_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open IsDedekindDomain NumberField.AdelicHaar MeasureTheory

noncomputable section
noncomputable section

namespace PlaceEmbedding

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem glFin_ext {x y : GL (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R, AdelicLevel.finComponent R K w x = AdelicLevel.finComponent R K w y) :
    x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine FiniteAdeleRing.ext (R := R) (K := K) fun w => ?_
  have hw := congrArg (fun z : GL (Fin 2) (w.adicCompletion K) =>
    (z : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) (h w)
  simpa only [AdelicLevel.finComponent_apply] using hw

private theorem adelicGL_ext {x y : GL (Fin 2) (AdeleRing R K)}
    (harch : AdelicLevel.glArch R K x = AdelicLevel.glArch R K y)
    (hfin : AdelicLevel.glFin R K x = AdelicLevel.glFin R K y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h₁ := congrArg (fun z : GL (Fin 2) (InfiniteAdeleRing K) =>
    (z : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) harch
  have h₂ := congrArg (fun z : GL (Fin 2) (FiniteAdeleRing R K) =>
    (z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) hfin
  simp only [AdelicLevel.glArch_apply, AdelicLevel.glFin_apply] at h₁ h₂
  exact Prod.ext h₁ h₂

variable (v : HeightOneSpectrum R)

private def ι : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (AdeleRing R K) :=
  (AdelicDock.finEmbed R K).comp (AdelicDock.localEmbed R K v)

private def compAt (g : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (v.adicCompletion K) :=
  AdelicLevel.finComponent R K v (AdelicLevel.glFin R K g)

private theorem compAt_apply (g : GL (Fin 2) (AdeleRing R K)) :
    compAt R K v g = AdelicLevel.finComponent R K v (AdelicLevel.glFin R K g) := rfl

private theorem compAt_mul (g g' : GL (Fin 2) (AdeleRing R K)) :
    compAt R K v (g * g') = compAt R K v g * compAt R K v g' := by
  simp only [compAt_apply, map_mul]

private theorem compAt_inv (g : GL (Fin 2) (AdeleRing R K)) : compAt R K v g⁻¹ = (compAt R K v g)⁻¹ := by
  simp only [compAt_apply, map_inv]

private theorem glArch_ι (h : GL (Fin 2) (v.adicCompletion K)) : AdelicLevel.glArch R K (ι R K v h) = 1 :=
  AdelicDock.glArch_finEmbed R K _

private theorem glFin_ι (h : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.glFin R K (ι R K v h) = AdelicDock.localEmbed R K v h :=
  AdelicDock.glFin_finEmbed R K _

private theorem compAt_ι (h : GL (Fin 2) (v.adicCompletion K)) : compAt R K v (ι R K v h) = h := by
  rw [compAt_apply, glFin_ι, AdelicDock.finComponent_localEmbed_self]

private theorem finComponent_glFin_ι_of_ne (h : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (AdelicLevel.glFin R K (ι R K v h)) = 1 := by
  rw [glFin_ι, AdelicDock.finComponent_localEmbed_of_ne R K v h hw]

private theorem inv_mul_ι_mul (g : GL (Fin 2) (AdeleRing R K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    g⁻¹ * ι R K v h * g = ι R K v ((compAt R K v g)⁻¹ * h * compAt R K v g) := by
  refine adelicGL_ext R K ?_ ?_
  · simp only [map_mul, map_inv, glArch_ι, mul_one, inv_mul_cancel, inv_one]
  · refine glFin_ext R K fun w => ?_
    by_cases hw : w = v
    · subst hw
      simp only [map_mul, map_inv, glFin_ι, AdelicDock.finComponent_localEmbed_self, compAt_apply]
    · have hne : ∀ x : GL (Fin 2) (v.adicCompletion K),
          AdelicLevel.finComponent R K w (AdelicDock.localEmbed R K v x) = 1 :=
        fun x => AdelicDock.finComponent_localEmbed_of_ne R K v x hw
      simp only [map_mul, map_inv, glFin_ι, hne, mul_one, inv_mul_cancel, inv_one]

private theorem mul_ι_conj (g : GL (Fin 2) (AdeleRing R K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    g * ι R K v ((compAt R K v g)⁻¹ * h * compAt R K v g) = ι R K v h * g := by
  rw [← inv_mul_ι_mul R K v g h, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem ι_mul_comm_of_compAt_eq_one {x : GL (Fin 2) (AdeleRing R K)} (hx : compAt R K v x = 1)
    (h : GL (Fin 2) (v.adicCompletion K)) : ι R K v h * x = x * ι R K v h := by
  have := mul_ι_conj R K v x h
  rw [hx, inv_one, one_mul, mul_one] at this
  exact this.symm

private def awayFrom (g : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (AdeleRing R K) :=
  g * (ι R K v (compAt R K v g))⁻¹

private theorem awayFrom_mul_ι_compAt (g : GL (Fin 2) (AdeleRing R K)) :
    awayFrom R K v g * ι R K v (compAt R K v g) = g :=
  inv_mul_cancel_right g _

private theorem compAt_awayFrom (g : GL (Fin 2) (AdeleRing R K)) : compAt R K v (awayFrom R K v g) = 1 := by
  rw [awayFrom, compAt_mul, compAt_inv, compAt_ι, mul_inv_cancel]

private theorem finComponent_glFin_awayFrom_of_ne (g : GL (Fin 2) (AdeleRing R K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (AdelicLevel.glFin R K (awayFrom R K v g))
      = AdelicLevel.finComponent R K w (AdelicLevel.glFin R K g) := by
  rw [awayFrom]
  simp only [map_mul, map_inv]
  rw [finComponent_glFin_ι_of_ne R K v _ hw, inv_one, mul_one]

private theorem glArch_awayFrom (g : GL (Fin 2) (AdeleRing R K)) :
    AdelicLevel.glArch R K (awayFrom R K v g) = AdelicLevel.glArch R K g := by
  rw [awayFrom]
  simp only [map_mul, map_inv, glArch_ι, inv_one, mul_one]

private theorem ι_mul_awayFrom_comm (g : GL (Fin 2) (AdeleRing R K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    ι R K v h * awayFrom R K v g = awayFrom R K v g * ι R K v h :=
  ι_mul_comm_of_compAt_eq_one R K v (compAt_awayFrom R K v g) h

end PlaceEmbedding

namespace LevelComponents

open IsDedekindDomain.HeightOneSpectrum HeckeIntegralSeam AdelicDock

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem mem_U_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      exact (mem_localLevelOne_iff (𝓞 F) F w (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
        (hfin w)
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · exact (mem_finiteAdelicGL2Subgroup_iff F h).mpr harch

private theorem components_of_mem_U {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    glArch (𝓞 F) F h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨(mem_finiteAdelicGL2Subgroup_iff F h).mp h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

private theorem comp_self (z : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = z := by
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem comp_of_ne (z : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = 1 := by
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

omit [NumberField F] in
private theorem ne_bot_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) : N ≠ ⊥ := by
  rintro rfl
  exact hv (dvd_zero _)

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v N m := by
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd (ne_bot_of_not_dvd F v hv) hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private theorem mem_localLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      i j ∈ v.adicCompletionIntegers F) :
    k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv hk, isLocalLevelOne_of_integral F v hv hk'⟩

private noncomputable abbrev wc (w : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (w.adicCompletion F) :=
  finComponent (𝓞 F) F w (glFin (𝓞 F) F (weyl (𝓞 F) F))

private theorem weyl_mul_self : weyl (𝓞 F) F * weyl (𝓞 F) F = 1 :=
  Units.ext (by simp [weyl, Matrix.one_fin_two])

private theorem wc_mul_self (w : HeightOneSpectrum (𝓞 F)) : wc F w * wc F w = 1 := by
  simp only [wc, ← map_mul, weyl_mul_self, map_one]

private theorem weyl_entry_mem (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (wc F w : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j ∈ w.adicCompletionIntegers F := by
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;>
    first
      | exact zero_mem_integralFiniteAdeles w
      | exact one_mem_integralFiniteAdeles w

private theorem wc_mem {N : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} (hw : ¬ w.asIdeal ∣ N) :
    wc F w ∈ localLevelOne (𝓞 F) F w N := by
  refine mem_localLevelOne_of_integral F w hw (weyl_entry_mem F w) fun i j => ?_
  rw [inv_eq_of_mul_eq_one_right (wc_mul_self F w)]
  exact weyl_entry_mem F w i j

private theorem comp_conj (w : HeightOneSpectrum (𝓞 F)) (h : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F))
      = (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w := by
  simp only [wc, map_mul, map_inv]

private theorem mem_P_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hU : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (hconj : ∀ w : HeightOneSpectrum (𝓞 F),
      (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hU
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 F) F N).mpr ⟨h1, ?_⟩, h2⟩
  have harch : glArch (𝓞 F) F h = 1 := (components_of_mem_U F hU).1
  have hz : (weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F ?_ fun w => ?_
    · simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
    · rw [comp_conj]
      exact hconj w
  refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F, (Subgroup.mem_inf.mp hz).1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem components_of_mem_P {N : Ideal (𝓞 F)} {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (w : HeightOneSpectrum (𝓞 F)) :
    (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p) * wc F w ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hp
  obtain ⟨-, hmap⟩ := (mem_principalLevel_iff (𝓞 F) F N).mp h1
  obtain ⟨z, hz, hzp⟩ := Subgroup.mem_map.mp hmap
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzp
  have hz' : (weyl (𝓞 F) F)⁻¹ * p * weyl (𝓞 F) F = z := by
    rw [← hzp]; group
  have harch : glArch (𝓞 F) F p = 1 := (mem_finiteAdelicGL2Subgroup_iff F p).mp h2
  have hzU : z ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine Subgroup.mem_inf.mpr ⟨hz, (mem_finiteAdelicGL2Subgroup_iff F z).mpr ?_⟩
    rw [← hz']
    simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
  rw [← comp_conj, hz']
  exact (components_of_mem_U F hzU).2 w

private theorem P_le_U (N : Ideal (𝓞 F)) :
    principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  inf_le_inf_right _ (principalLevel_le_levelOne (𝓞 F) F N)

private theorem supported_mem_P {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {z : GL (Fin 2) (v.adicCompletion F)} (hz : z ∈ localLevelOne (𝓞 F) F v N) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z) ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  have hU : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F (glArch_finEmbed _ _ _) fun w => ?_
    by_cases hw : w = v
    · rw [hw, comp_self]
      exact hz
    · rw [comp_of_ne F v z hw]
      exact one_mem _
  refine mem_P_of_components F hU fun w => ?_
  by_cases hw : w = v
  · rw [hw, comp_self]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (wc_mem F hv)) hz) (wc_mem F hv)
  · rw [comp_of_ne F v z hw, mul_one, inv_mul_cancel]
    exact one_mem _

section Transfer

open LocalGL2

private theorem isHeckeCosetSystem_principal_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    (d : GL (Fin 2) (v.adicCompletion F)) {ι : Type} (r : ι → GL (Fin 2) (v.adicCompletion F))
    (hsys : IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v d))
      (fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i)))) :
    IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v d))
      (fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i))) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  ·
    obtain ⟨u₁, hu₁, u₂, hu₂, hrep⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    set a₁ := finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁) with ha₁
    set a₂ := finComponent (𝓞 F) F v (glFin (𝓞 F) F u₂) with ha₂
    have hloc : a₁ * d * a₂ = r i := by
      have h := congrArg (fun y => finComponent (𝓞 F) F v (glFin (𝓞 F) F y)) hrep
      simpa only [map_mul, comp_self] using h
    refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v a₁),
        supported_mem_P F v hv ((components_of_mem_U F hu₁).2 v),
        finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v a₂),
        supported_mem_P F v hv ((components_of_mem_U F hu₂).2 v), ?_⟩
    simp only [← map_mul, hloc]
  ·
    have hxU : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v d)) := by
      obtain ⟨p₁, hp₁, p₂, hp₂, hxeq⟩ := HeckePair.mem_doubleCoset_iff.mp hx
      exact HeckePair.mem_doubleCoset_iff.mpr ⟨p₁, P_le_U F N hp₁, p₂, P_le_U F N hp₂, hxeq⟩
    obtain ⟨i, hi⟩ := hsys.covers x hxU
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    obtain ⟨p₁, hp₁, p₂, hp₂, hxeq⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    refine mem_P_of_components F hi fun w => ?_
    by_cases hw : w = v
    · rw [hw]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (wc_mem F hv))
        ((components_of_mem_U F hi).2 v)) (wc_mem F hv)
    · have hx' : finComponent (𝓞 F) F w (glFin (𝓞 F) F x)
          = finComponent (𝓞 F) F w (glFin (𝓞 F) F p₁) * finComponent (𝓞 F) F w (glFin (𝓞 F) F p₂) := by
        rw [← hxeq]
        simp only [map_mul, comp_of_ne F v d hw, mul_one]
      have hr : finComponent (𝓞 F) F w (glFin (𝓞 F) F
          (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i)))) = 1 := comp_of_ne F v (r i) hw
      simp only [map_mul, map_inv, hx', hr, mul_one, mul_inv_rev]
      have h₁ := components_of_mem_P F hp₁ w
      have h₂ := components_of_mem_P F hp₂ w
      have key : (wc F w)⁻¹ * ((finComponent (𝓞 F) F w (glFin (𝓞 F) F p₂))⁻¹
            * (finComponent (𝓞 F) F w (glFin (𝓞 F) F p₁))⁻¹) * wc F w
          = ((wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p₂) * wc F w)⁻¹
            * ((wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p₁) * wc F w)⁻¹ := by
        group
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) (Subgroup.inv_mem _ h₁)
  ·
    apply hsys.mk_injective
    simp only at hij ⊢
    rw [QuotientGroup.eq] at hij ⊢
    exact P_le_U F N hij

private theorem reindex {G : Type} [Group G] {U : Subgroup G} {g : G} {ι κ : Type} {reps : ι → G}
    (h : IsHeckeCosetSystem U g reps) (e : κ ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (h.mk_injective hkk')

private theorem card_option_quotient [Fintype (𝓞 F ⧸ v.asIdeal)] :
    Fintype.card (Option (𝓞 F ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
  rw [Fintype.card_option, ← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Transfer

end LevelComponents

namespace LocalOrbit

open PlaceEmbedding

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def nU (b : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private def nL (c : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

@[scoped simp] private theorem nU_coe (b : v.adicCompletion K) :
    (nU v b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, b; 0, 1] := rfl

@[scoped simp] private theorem nL_coe (c : v.adicCompletion K) :
    (nL v c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; c, 1] := rfl

@[scoped simp] private theorem nU_zero : nU v 0 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

@[scoped simp] private theorem nL_zero : nL v 0 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

private theorem exp_neg_le_one (n : ℕ) : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private def Cong (m : ℕ) (g : GL (Fin 2) (v.adicCompletion K)) : Prop :=
  ∀ i j : Fin 2, Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j - (1 : Matrix (Fin 2) (Fin 2)
    (v.adicCompletion K)) i j) ≤ AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ m) v

private theorem idealBound_pow (m : ℕ) :
    AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ m) v = WithZero.exp (-(m : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (pow_ne_zero m v.ne_bot)]
  congr 2
  simp only [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) v.associates_irreducible,
    Associates.count_self v.associates_irreducible, mul_one]

private theorem cong_iff (m : ℕ) (g : GL (Fin 2) (v.adicCompletion K)) :
    Cong v m g ↔ ∀ i j : Fin 2, Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(m : ℤ)) := by
  unfold Cong
  rw [idealBound_pow]

private theorem cong_mono
    {m m' : ℕ} (hmm : m ≤ m') {g : GL (Fin 2) (v.adicCompletion K)} (h : Cong v m' g) : Cong v m g := by
  rw [cong_iff] at h ⊢
  intro i j
  refine (h i j).trans ?_
  rw [WithZero.exp_le_exp]
  omega

private theorem exists_nat_valued_le (x : v.adicCompletion K) : ∃ n : ℕ, Valued.v x ≤ WithZero.exp (n : ℤ) := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hx]
    rw [WithZero.exp_le_exp]
    exact Int.self_le_toNat _

private theorem exists_nat_forall_valued_le (s : Finset (v.adicCompletion K)) :
    ∃ n : ℕ, ∀ x ∈ s, Valued.v x ≤ WithZero.exp (n : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert a s _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨na, hna⟩ := exists_nat_valued_le v a
    refine ⟨max n na, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hna.trans (by rw [WithZero.exp_le_exp]; exact_mod_cast le_max_right n na)
    · exact (hn x hx).trans (by rw [WithZero.exp_le_exp]; exact_mod_cast le_max_left n na)

private theorem exists_entry_bound (h : GL (Fin 2) (v.adicCompletion K)) :
    ∃ n : ℕ, (∀ i j, Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (n : ℤ)) ∧
      ∀ i j, Valued.v (((h⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
        ≤ WithZero.exp (n : ℤ) := by
  classical
  let s : Finset (v.adicCompletion K) :=
    (Finset.univ : Finset (Fin 2 × Fin 2)).image
        (fun p => (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) p.1 p.2) ∪
      (Finset.univ : Finset (Fin 2 × Fin 2)).image
        (fun p => ((h⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) p.1 p.2)
  obtain ⟨n, hn⟩ := exists_nat_forall_valued_le v s
  refine ⟨n, fun i j => hn _ ?_, fun i j => hn _ ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))

private theorem entry_mul_le {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} {α β : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ α) (hB : ∀ i j, Valued.v (B i j) ≤ β) :
    ∀ i j, Valued.v ((A * B) i j) ≤ α * β := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;>
    exact mul_le_mul' (hA _ _) (hB _ _)

private theorem conj_sub_one (h k : GL (Fin 2) (v.adicCompletion K)) :
    ((h⁻¹ * k * h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1 =
      ((h⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) - 1) *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]

private theorem cong_conj {n m : ℕ} {h k : GL (Fin 2) (v.adicCompletion K)}
    (hh : ∀ i j, Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (n : ℤ))
    (hh' : ∀ i j,
      Valued.v (((h⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
        ≤ WithZero.exp (n : ℤ))
    (hk : Cong v (m + 2 * n) k) : Cong v m (h⁻¹ * k * h) := by
  rw [cong_iff] at hk ⊢
  have hk' : ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j)
      ≤ WithZero.exp (-((m + 2 * n : ℕ) : ℤ)) := fun i j => by
    rw [Matrix.sub_apply]; exact hk i j
  have h1 := entry_mul_le v hh' hk'
  have h2 := entry_mul_le v h1 hh
  intro i j
  rw [← Matrix.sub_apply, conj_sub_one]
  refine (h2 i j).trans (le_of_eq ?_)
  rw [← WithZero.exp_add, ← WithZero.exp_add]
  congr 1
  push_cast
  ring

private theorem cong_inv
    {m : ℕ} (hm : 1 ≤ m) {k : GL (Fin 2) (v.adicCompletion K)} (hk : Cong v m k) : Cong v m k⁻¹ := by
  rw [cong_iff] at hk ⊢

  have hsub : ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j)
      ≤ WithZero.exp (-(m : ℤ)) := fun i j => by rw [Matrix.sub_apply]; exact hk i j

  obtain ⟨B, hB, hBle⟩ : ∃ B : WithZero (Multiplicative ℤ),
      (∀ i j, Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
        ≤ B) ∧
      ∀ C : WithZero (Multiplicative ℤ),
        (∀ i j, Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
          ≤ C) → B ≤ C := by
    let e : Fin 2 → Fin 2 → WithZero (Multiplicative ℤ) := fun i j =>
      Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
    refine ⟨max (max (e 0 0) (e 0 1)) (max (e 1 0) (e 1 1)), fun i j => ?_, fun C hC => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [e]
    · exact max_le (max_le (hC 0 0) (hC 0 1)) (max_le (hC 1 0) (hC 1 1))

  have hid : ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1 =
      -(((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) - 1)) := by
    rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
  have hdiff : ∀ i j, Valued.v ((((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2)
      (v.adicCompletion K)) - 1) i j) ≤ B * WithZero.exp (-(m : ℤ)) := by
    intro i j
    rw [hid, Matrix.neg_apply, Valuation.map_neg]
    exact entry_mul_le v hB hsub i j

  have hBmax : B ≤ max 1 (B * WithZero.exp (-(m : ℤ))) := by
    refine hBle _ fun i j => ?_
    have hsplit : ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
        (((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j +
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [hsplit]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · exact (hdiff i j).trans (le_max_right _ _)
    · refine le_trans ?_ (le_max_left _ _)
      by_cases hij : i = j
      · rw [hij, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hij, map_zero]; exact zero_le'

  have hB1 : B ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hB0 : B ≠ 0 := fun h0 => by rw [h0] at hlt; exact (not_lt_of_ge zero_le') hlt
    have hlog := WithZero.exp_log hB0
    have hmul : B * WithZero.exp (-(m : ℤ)) < B := by
      rw [← hlog, ← WithZero.exp_add, WithZero.exp_lt_exp]
      omega
    have h1B : (1 : WithZero (Multiplicative ℤ)) < B := hlt
    exact (lt_irrefl B) (hBmax.trans_lt (max_lt h1B hmul))
  intro i j
  rw [← Matrix.sub_apply]
  refine (hdiff i j).trans ?_
  calc B * WithZero.exp (-(m : ℤ)) ≤ 1 * WithZero.exp (-(m : ℤ)) := mul_le_mul' hB1 le_rfl
    _ = WithZero.exp (-(m : ℤ)) := one_mul _

private theorem isLocalLevelOne_of_cong {A : Ideal (𝓞 K)} {M : ℕ}
    (hMA : WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) A v)
    {g : GL (Fin 2) (v.adicCompletion K)} (hg : Cong v M g) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v A (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [cong_iff] at hg
  have hle1 : WithZero.exp (-(M : ℤ)) ≤ 1 := exp_neg_le_one M
  have hentry : ∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 := by
    intro i j
    have hsplit : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
        ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
          + (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := (sub_add_cancel _ _).symm
    rw [hsplit]
    refine (Valuation.map_add _ _ _).trans (max_le ((hg i j).trans hle1) ?_)
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, map_zero]; exact zero_le'
  refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr (hentry i j), ?_, ?_⟩
  · have h10 := hg 1 0
    rw [Matrix.one_apply_ne (by decide), sub_zero] at h10
    exact h10.trans hMA
  · have h11 := hg 1 1
    rw [Matrix.one_apply_eq] at h11
    exact h11.trans hMA

private theorem mem_localLevelOne_of_cong {A : Ideal (𝓞 K)} {M : ℕ} (hM1 : 1 ≤ M)
    (hMA : WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) A v)
    {g : GL (Fin 2) (v.adicCompletion K)} (hg : Cong v M g) : g ∈ AdelicDock.localLevelOne (𝓞 K) K v A :=
  (AdelicDock.mem_localLevelOne_iff (𝓞 K) K v g).mpr
    ⟨isLocalLevelOne_of_cong v hMA hg, isLocalLevelOne_of_cong v hMA (cong_inv v hM1 hg)⟩

private theorem exists_exp_neg_le_idealBound {A : Ideal (𝓞 K)} (hA : A ≠ ⊥) :
    ∃ M : ℕ, WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) A v :=
  ⟨(Associates.mk v.asIdeal).count (Associates.mk A).factors, by rw [AdelicLevel.idealBound_of_ne_bot hA]⟩

private theorem cong_weyl_conj {M : ℕ} {g : GL (Fin 2) (v.adicCompletion K)} (hg : Cong v M g) :
    Cong v M ((LevelComponents.wc K v)⁻¹ * g * LevelComponents.wc K v) := by
  have hw : ∀ i j, Valued.v ((LevelComponents.wc K v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      ≤ WithZero.exp ((0 : ℕ) : ℤ) := fun i j => by
    rw [Nat.cast_zero, WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (LevelComponents.weyl_entry_mem K v i j)
  have hw' : ∀ i j, Valued.v ((((LevelComponents.wc K v)⁻¹ : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp ((0 : ℕ) : ℤ) := by
    rw [inv_eq_of_mul_eq_one_right (LevelComponents.wc_mul_self K v)]
    exact hw
  exact cong_conj v hw hw' (by simpa using hg)

private theorem ι_mem_level_of_cong {D B : Ideal (𝓞 K)} {M : ℕ} (hM1 : 1 ≤ M)
    (hMD : WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) D v)
    (hMB : WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) B v)
    {g : GL (Fin 2) (v.adicCompletion K)} (hg : Cong v M g) :
    ι (𝓞 K) K v g ∈ AdelicLevel.levelOne (𝓞 K) K D ⊓ AdelicLevel.principalLevel (𝓞 K) K B ⊓
      AutomorphicForm.finiteAdelicGL2Subgroup K := by
  have hU : ∀ A : Ideal (𝓞 K), WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) A v →
      ι (𝓞 K) K v g ∈ AdelicLevel.levelOne (𝓞 K) K A ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by
    intro A hMA
    refine LevelComponents.mem_U_of_components K (glArch_ι (𝓞 K) K v g) fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [glFin_ι, AdelicDock.finComponent_localEmbed_self]
      exact mem_localLevelOne_of_cong _ hM1 hMA hg
    · rw [finComponent_glFin_ι_of_ne (𝓞 K) K _ g hw]
      exact one_mem _
  have hP : ι (𝓞 K) K v g ∈
      AdelicLevel.principalLevel (𝓞 K) K B ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by
    refine LevelComponents.mem_P_of_components K (hU B hMB) fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [glFin_ι, AdelicDock.finComponent_localEmbed_self]
      exact mem_localLevelOne_of_cong _ hM1 hMB (cong_weyl_conj _ hg)
    · rw [finComponent_glFin_ι_of_ne (𝓞 K) K _ g hw, mul_one, inv_mul_cancel]
      exact one_mem _
  obtain ⟨hD', hfin⟩ := Subgroup.mem_inf.mp (hU D hMD)
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hD', (Subgroup.mem_inf.mp hP).1⟩, hfin⟩

section OrbitSpan

variable (Φ₀ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)

private def rightRepAt : Representation ℂ (GL (Fin 2) (v.adicCompletion K)) (GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) where
  toFun k :=
    { toFun := fun φ x => φ (x * ι (𝓞 K) K v k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change φ (x * ι (𝓞 K) K v 1) = φ x
    rw [map_one, mul_one]
  map_mul' a b := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change φ (x * ι (𝓞 K) K v (a * b)) = φ (x * ι (𝓞 K) K v a * ι (𝓞 K) K v b)
    rw [map_mul, mul_assoc]

@[scoped simp] private theorem rightRepAt_apply (k : GL (Fin 2) (v.adicCompletion K)) (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) : rightRepAt v k φ x = φ (x * ι (𝓞 K) K v k) :=
  rfl

private def orbitGen (h : GL (Fin 2) (v.adicCompletion K)) : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun x => Φ₀ (x * ι (𝓞 K) K v h)

private theorem orbitGen_apply (h : GL (Fin 2) (v.adicCompletion K)) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    orbitGen v Φ₀ h x = Φ₀ (x * ι (𝓞 K) K v h) :=
  rfl

private theorem rightRepAt_orbitGen (k h : GL (Fin 2) (v.adicCompletion K)) :
    rightRepAt v k (orbitGen v Φ₀ h) = orbitGen v Φ₀ (k * h) := by
  funext x
  rw [rightRepAt_apply, orbitGen_apply, orbitGen_apply, map_mul, mul_assoc]

private def orbitSpan : Submodule ℂ (GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :=
  Submodule.span ℂ (Set.range (orbitGen v Φ₀))

private theorem orbitGen_mem (h : GL (Fin 2) (v.adicCompletion K)) : orbitGen v Φ₀ h ∈ orbitSpan v Φ₀ :=
  Submodule.subset_span ⟨h, rfl⟩

private theorem self_mem_orbitSpan : Φ₀ ∈ orbitSpan v Φ₀ := by
  have h : orbitGen v Φ₀ 1 = Φ₀ := by
    funext x
    rw [orbitGen_apply, map_one, mul_one]
  have hmem := orbitGen_mem v Φ₀ 1
  rwa [h] at hmem

private theorem orbitSpan_stable (k : GL (Fin 2) (v.adicCompletion K)) :
    ∀ φ ∈ orbitSpan v Φ₀, rightRepAt v k φ ∈ orbitSpan v Φ₀ := by
  intro φ hφ
  have hle : (orbitSpan v Φ₀).map (rightRepAt v k) ≤ orbitSpan v Φ₀ := by
    refine Submodule.map_span_le _ _ _ |>.mpr ?_
    rintro _ ⟨h, rfl⟩
    rw [rightRepAt_orbitGen]
    exact orbitGen_mem v Φ₀ _
  exact hle (Submodule.mem_map_of_mem hφ)

private def orbitRep : Representation ℂ (GL (Fin 2) (v.adicCompletion K)) (orbitSpan v Φ₀) where
  toFun k := (rightRepAt v k).restrict (orbitSpan_stable v Φ₀ k)
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change rightRepAt v 1 (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) = w
    rw [map_one]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change rightRepAt v (a * b) (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) =
      rightRepAt v a (rightRepAt v b (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ))
    rw [map_mul]
    rfl

@[scoped simp] private theorem coe_orbitRep_apply (k : GL (Fin 2) (v.adicCompletion K)) (w : orbitSpan v Φ₀) :
    ((orbitRep v Φ₀ k w : orbitSpan v Φ₀) : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) =
      rightRepAt v k (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :=
  rfl

private theorem orbitRep_smooth {M : ℕ}
    (hΦ : ∀ g : GL (Fin 2) (v.adicCompletion K), Cong v M g → ∀ x, Φ₀ (x * ι (𝓞 K) K v g) = Φ₀ x) :
    ∀ w : orbitSpan v Φ₀, ∃ m : ℕ, ∀ g : GL (Fin 2) (v.adicCompletion K), Cong v m g → orbitRep v Φ₀ g w = w := by
  suffices h : ∀ φ ∈ orbitSpan v Φ₀, ∃ m : ℕ, ∀ g : GL (Fin 2) (v.adicCompletion K),
      Cong v m g → rightRepAt v g φ = φ by
    intro w
    obtain ⟨m, hm⟩ := h w w.2
    exact ⟨m, fun g hg => Subtype.ext (hm g hg)⟩
  intro φ hφ
  refine Submodule.span_induction (p := fun φ _ => ∃ m : ℕ, ∀ g : GL (Fin 2) (v.adicCompletion K),
      Cong v m g → rightRepAt v g φ = φ) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨h, rfl⟩
    obtain ⟨n, hh, hh'⟩ := exists_entry_bound v h
    refine ⟨M + 2 * n, fun g hg => funext fun x => ?_⟩
    rw [rightRepAt_apply, orbitGen_apply, orbitGen_apply]
    have hc : Cong v M (h⁻¹ * g * h) := cong_conj v hh hh' hg
    have hx := hΦ _ hc (x * ι (𝓞 K) K v h)
    rw [map_mul, map_mul, map_inv, mul_assoc, mul_assoc, mul_inv_cancel_left] at hx
    rw [mul_assoc]
    exact hx
  · exact ⟨0, fun g _ => map_zero _⟩
  · rintro φ ψ - - ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    refine ⟨max m₁ m₂, fun g hg => ?_⟩
    rw [map_add, h₁ g (cong_mono v (le_max_left _ _) hg), h₂ g (cong_mono v (le_max_right _ _) hg)]
  · rintro c φ - ⟨m, hm⟩
    exact ⟨m, fun g hg => by rw [map_smul, hm g hg]⟩

end OrbitSpan

private theorem idealBound_anti {M N : Ideal (𝓞 K)} (hMN : M ∣ N) (hN : N ≠ ⊥) :
    AdelicLevel.idealBound (𝓞 K) N v ≤ AdelicLevel.idealBound (𝓞 K) M v := by
  classical
  have hM : M ≠ ⊥ := by
    rintro rfl
    obtain ⟨k, rfl⟩ := hMN
    exact hN (Ideal.bot_mul k)
  rw [AdelicLevel.idealBound_of_ne_bot hN, AdelicLevel.idealBound_of_ne_bot hM, WithZero.exp_le_exp, neg_le_neg_iff]
  exact_mod_cast Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hN) v.associates_irreducible
    (Associates.mk_le_mk_of_dvd hMN)

private theorem isLocalLevelOne_of_dvd {M N : Ideal (𝓞 K)} (hMN : M ∣ N) (hN : N ≠ ⊥)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (h : AdelicDock.IsLocalLevelOne (𝓞 K) K v N m) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v M m :=
  ⟨h.integral, h.lowerLeft.trans (idealBound_anti v hMN hN), h.lowerRight.trans (idealBound_anti v hMN hN)⟩

private theorem localLevelOne_anti {M N : Ideal (𝓞 K)} (hMN : M ∣ N) (hN : N ≠ ⊥) :
    AdelicDock.localLevelOne (𝓞 K) K v N ≤ AdelicDock.localLevelOne (𝓞 K) K v M := by
  intro g hg
  rw [AdelicDock.mem_localLevelOne_iff] at hg ⊢
  exact ⟨isLocalLevelOne_of_dvd v hMN hN hg.1, isLocalLevelOne_of_dvd v hMN hN hg.2⟩

private theorem wc_apply (i j : Fin 2) :
    ((LevelComponents.wc K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem wc_conj_apply (g : GL (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    ((((LevelComponents.wc K v)⁻¹ * g * LevelComponents.wc K v : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
      = (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (Equiv.swap 0 1 i) (Equiv.swap 0 1 j) := by
  rw [inv_eq_of_mul_eq_one_right (LevelComponents.wc_mul_self K v)]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, wc_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem entries_of_levelOne_of_conj {N : Ideal (𝓞 K)} {g : GL (Fin 2) (v.adicCompletion K)}
    (hU : g ∈ AdelicDock.localLevelOne (𝓞 K) K v N)
    (hP : (LevelComponents.wc K v)⁻¹ * g * LevelComponents.wc K v ∈ AdelicDock.localLevelOne (𝓞 K) K v N)
    (i j : Fin 2) :
    Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ AdelicLevel.idealBound (𝓞 K) N v := by
  rw [AdelicDock.mem_localLevelOne_iff] at hU hP
  obtain ⟨hU1, -⟩ := hU
  obtain ⟨hP1, -⟩ := hP
  have e10 := wc_conj_apply v g 1 0
  have e11 := wc_conj_apply v g 1 1
  simp only [Equiv.swap_apply_right, Equiv.swap_apply_left] at e10 e11
  fin_cases i <;> fin_cases j
  · have h := hP1.lowerRight
    rw [e11] at h
    simpa [Matrix.one_apply_eq] using h
  · have h := hP1.lowerLeft
    rw [e10] at h
    simpa [Matrix.one_apply_ne] using h
  · simpa [Matrix.one_apply_ne] using hU1.lowerLeft
  · simpa [Matrix.one_apply_eq] using hU1.lowerRight

end LocalOrbit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section
open IsDedekindDomain NumberField AutomorphicForm FLT.SmoothVectors
open scoped Topology Pointwise

namespace SmoothConvolution

private theorem exists_isOpen_one_mem_forall_mul_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ff : G → ℂ) (hlc : IsLocallyConstant ff) (hsupp : HasCompactSupport ff) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ w ∈ V, ∀ y : G, ff (w * y) = ff y := by

  have hmap : IsLocallyConstant fun p : G × G => (ff (p.1 * p.2), ff p.2) :=
    (hlc.comp_continuous continuous_mul).prodMk (hlc.comp_continuous continuous_snd)
  have hO : IsOpen ((fun p : G × G => (ff (p.1 * p.2), ff p.2)) ⁻¹' {q : ℂ × ℂ | q.1 = q.2}) :=
    hmap {q : ℂ × ℂ | q.1 = q.2}

  have hsub : ({(1 : G)} : Set G) ×ˢ tsupport ff
      ⊆ (fun p : G × G => (ff (p.1 * p.2), ff p.2)) ⁻¹' {q : ℂ × ℂ | q.1 = q.2} := by
    rintro ⟨w, y⟩ ⟨hw, -⟩
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simp only [Set.mem_preimage, Set.mem_setOf_eq, one_mul]
  obtain ⟨u, t, hu, -, h1u, hCt, hut⟩ :=
    generalized_tube_lemma isCompact_singleton hsupp hO hsub
  have h1 : (1 : G) ∈ u := h1u rfl
  refine ⟨u ∩ u⁻¹, hu.inter hu.inv, ⟨h1, by simpa using h1⟩, ?_⟩
  rintro w ⟨hwu, hwinv⟩ y
  have hagree : ∀ w' ∈ u, ∀ y' ∈ tsupport ff, ff (w' * y') = ff y' := fun w' hw' y' hy' =>
    hut (Set.mk_mem_prod hw' (hCt hy'))
  by_cases hy : y ∈ tsupport ff
  · exact hagree w hwu y hy
  · by_cases hwy : w * y ∈ tsupport ff
    · have := hagree w⁻¹ (Set.mem_inv.mp hwinv) (w * y) hwy
      rw [inv_mul_cancel_left] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hwy]

variable {K : Type} [Field K] [NumberField K]

private theorem isKfSmooth_rightConv (u f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    IsKfSmooth K (rightConv K u f) := by
  obtain ⟨fa, ff, -, ⟨hlc, hsupp⟩, hprod⟩ := hf
  obtain ⟨V, hVopen, h1V, hV⟩ := exists_isOpen_one_mem_forall_mul_eq ff hlc hsupp

  have hfinv : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ finiteAdelicGL2Subgroup K →
      (AdelicLevel.glFin (𝓞 K) K k)⁻¹ ∈ V → ∀ y, f (k⁻¹ * y) = f y := by
    intro k hk hkV y
    rw [hprod, hprod, map_mul, map_mul, map_inv, map_inv, (mem_finiteAdelicGL2Subgroup_iff K k).mp hk,
      inv_one, one_mul, hV _ hkV]

  have hconv : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ finiteAdelicGL2Subgroup K →
      (AdelicLevel.glFin (𝓞 K) K k)⁻¹ ∈ V → ∀ g, rightConv K u f (g * k) = rightConv K u f g := by
    intro k hk hkV g
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
    congr 1
    funext y
    exact hfinv k hk hkV y

  unfold IsKfSmooth IsSmoothVector
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hN : IsOpen {k : finiteAdelicGL2Subgroup K | (AdelicLevel.glFin (𝓞 K) K (k : AdelicGL2 (𝓞 K) K))⁻¹ ∈ V} :=
    hVopen.preimage (((AdelicLevel.continuous_glFin (𝓞 K) K).comp continuous_subtype_val).inv)
  have h1N : (1 : finiteAdelicGL2Subgroup K)
      ∈ {k : finiteAdelicGL2Subgroup K | (AdelicLevel.glFin (𝓞 K) K (k : AdelicGL2 (𝓞 K) K))⁻¹ ∈ V} := by
    simpa using h1V
  refine Filter.mem_of_superset (hN.mem_nhds h1N) ?_
  intro k hk
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  refine RightTranslationFn.ext fun g => ?_
  rw [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
  exact hconv k k.2 hk g

end SmoothConvolution
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

namespace IsotypicConvolution

section Basics

variable {K : Type} [Field K] [NumberField K]

private theorem continuous_val_finEmbed :
    Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      ((AdelicDock.finEmbed (𝓞 K) K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_const.prodMk (Units.continuous_val.matrix_elem i j)

private theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 K) K) :=
  Units.continuous_iff.mpr ⟨continuous_val_finEmbed,
    (continuous_val_finEmbed.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, map_inv]⟩

private theorem val_adelicArchGLIncl_apply (k : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      ((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

private theorem continuous_val_adelicArchGLIncl :
    Continuous fun k : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [val_adelicArchGLIncl_apply]
  exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl K) :=
  Units.continuous_iff.mpr ⟨continuous_val_adelicArchGLIncl,
    (continuous_val_adelicArchGLIncl.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, map_inv]⟩

private theorem adelicGL_ext' {x y : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (h₂ : glFin (𝓞 K) K x = glFin (𝓞 K) K y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · simpa only [glArch_apply] using
      congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing K) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  · simpa only [glFin_apply] using
      congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₂

private theorem eq_archIncl_mul_finEmbed (x : AdelicGL2 (𝓞 K) K) :
    x = adelicArchGLIncl K (glArch (𝓞 K) K x) * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K x) :=
  adelicGL_ext'
    (by rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one])
    (by rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul])

open scoped Classical in
private theorem continuous_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) :
    Continuous f := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩, ⟨hffl, -⟩, hfg⟩ := hf
  have hfa : Continuous fa := by
    rw [show fa = fun g => Φ (archEntries K g) from funext hfaΦ]
    refine hΦ.continuous.comp ?_
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)
  rw [show f = fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) from funext hfg]
  exact (hfa.comp (continuous_glArch (𝓞 K) K)).mul (hffl.continuous.comp (continuous_glFin (𝓞 K) K))

private theorem hasCompactSupport_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) :
    HasCompactSupport f := by
  obtain ⟨fa, ff, ⟨-, hfa⟩, ⟨-, hff⟩, hfg⟩ := hf
  have hK : IsCompact ((fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      adelicArchGLIncl K p.1 * AdelicDock.finEmbed (𝓞 K) K p.2) '' (tsupport fa ×ˢ tsupport ff)) :=
    (hfa.isCompact.prod hff.isCompact).image
      ((continuous_adelicArchGLIncl.comp continuous_fst).mul (continuous_finEmbed.comp continuous_snd))
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_cases ha : glArch (𝓞 K) K x ∈ tsupport fa
  · by_cases hb : glFin (𝓞 K) K x ∈ tsupport ff
    · exact absurd ⟨(glArch (𝓞 K) K x, glFin (𝓞 K) K x), ⟨ha, hb⟩, (eq_archIncl_mul_finEmbed x).symm⟩ hx
    · exact IsFactorizableTestFn.eq_zero_of_glFin K hfg (image_eq_zero_of_notMem_tsupport hb)
  · exact IsFactorizableTestFn.eq_zero_of_glArch K hfg (image_eq_zero_of_notMem_tsupport ha)

end Basics
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

end IsotypicConvolution
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section
open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped Topology

namespace OrbitCombination

open PlaceEmbedding

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isLocallyConstant_hasCompactSupport_comb (g : G → ℂ) (hlc : IsLocallyConstant g)
    (hsupp : HasCompactSupport g) {J : Type*} (s : Finset J) (c : J → ℂ) (t : J → G) :
    IsLocallyConstant (fun y : G => ∑ j ∈ s, c j * g (t j * y)) ∧
      HasCompactSupport (fun y : G => ∑ j ∈ s, c j * g (t j * y)) := by
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hj : ∀ j ∈ s, ∀ᶠ y' in 𝓝 y, g (t j * y') = g (t j * y) := by
      intro j _
      have h1 : IsLocallyConstant fun y' : G => g (t j * y') :=
        hlc.comp_continuous (continuous_const.mul continuous_id)
      exact (IsLocallyConstant.iff_eventually_eq _).mp h1 y
    filter_upwards [(s.eventually_all).mpr hj] with y' hy'
    exact Finset.sum_congr rfl fun j hjs => by rw [hy' j hjs]
  · refine HasCompactSupport.intro (s.isCompact_biUnion fun j _ =>
      (Homeomorph.mulLeft (t j)).isCompact_preimage.mpr hsupp) fun y hy => ?_
    refine Finset.sum_eq_zero fun j hjs => ?_
    have hy' : t j * y ∉ tsupport g := fun hmem => hy (Set.mem_biUnion hjs hmem)
    rw [image_eq_zero_of_notMem_tsupport hy', mul_zero]

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section Combination

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem isUnitFactorizableAt_comb {S : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∈ S)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableAt K ⊥ S f)
    {J : Type*} (s : Finset J) (c : J → ℂ) (h : J → GL (Fin 2) (v.adicCompletion K)) :
    IsUnitFactorizableAt K ⊥ S (fun x => ∑ j ∈ s, c j * f ((ι (𝓞 K) K v (h j))⁻¹ * x)) := by
  classical
  obtain ⟨-, fa, ff, fS, hfa, hff, hfS, hprod, hzero, hfeq⟩ := hf

  set t : J → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) := fun j => (AdelicDock.localEmbed (𝓞 K) K v (h j))⁻¹ with ht
  have ht_self : ∀ j, AdelicLevel.finComponent (𝓞 K) K v (t j) = (h j)⁻¹ := by
    intro j
    simp only [ht, map_inv, AdelicDock.finComponent_localEmbed_self]
  have ht_ne : ∀ j, ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → AdelicLevel.finComponent (𝓞 K) K w (t j) = 1 := by
    intro j w hw
    simp only [ht, map_inv, AdelicDock.finComponent_localEmbed_of_ne (𝓞 K) K v _ hw, inv_one]
  have hcomp_ne : ∀ j, ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → ∀ y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      AdelicLevel.finComponent (𝓞 K) K w (t j * y) = AdelicLevel.finComponent (𝓞 K) K w y := by
    intro j w hw y
    rw [map_mul, ht_ne j w hw, one_mul]
  have hcomp_self : ∀ j, ∀ y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      AdelicLevel.finComponent (𝓞 K) K v (t j * y) = (h j)⁻¹ * AdelicLevel.finComponent (𝓞 K) K v y := by
    intro j y
    rw [map_mul, ht_self]

  have hoffS : ∀ j, ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ∀ y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      AdelicLevel.finComponent (𝓞 K) K w (t j * y) = AdelicLevel.finComponent (𝓞 K) K w y :=
    fun j w hw y => hcomp_ne j w (fun hwv => hw (hwv ▸ hv)) y
  refine ⟨isBiInvariantUnder_bot K _, fa, fun y => ∑ j ∈ s, c j * ff (t j * y),
    Function.update fS v (fun z => ∑ j ∈ s, c j * fS v ((h j)⁻¹ * z)), hfa,
    isLocallyConstant_hasCompactSupport_comb ff hff.1 hff.2 s c t, ?_, ?_, ?_, ?_⟩
  ·
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self]
      exact isLocallyConstant_hasCompactSupport_comb (fS w) (hfS w hw).1 (hfS w hw).2 s c fun j => (h j)⁻¹
    · rw [Function.update_of_ne hwv]
      exact hfS w hw
  ·
    intro y hy
    have hy' : ∀ j, ∀ w ∉ S, AdelicLevel.finComponent (𝓞 K) K w (t j * y) ∈ localIntegralSet K w := by
      intro j w hw
      rw [hoffS j w hw]
      exact hy w hw
    rw [← Finset.mul_prod_erase S _ hv, Function.update_self, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hjs => ?_
    rw [hprod (t j * y) (hy' j), ← Finset.mul_prod_erase S _ hv, hcomp_self, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwv : w ≠ v := Finset.ne_of_mem_erase hw
    rw [Function.update_of_ne hwv, hcomp_ne j w hwv]
  ·
    rintro y ⟨w, hw, hyw⟩
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hzero (t j * y) ⟨w, hw, by rwa [hoffS j w hw]⟩, mul_zero]
  ·
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfeq, map_mul, map_mul, map_inv, map_inv, glArch_ι, inv_one, one_mul, glFin_ι, mul_left_comm]

private theorem ι_mul_comm_of_glFin_eq_one {a : GL (Fin 2) (AdeleRing (𝓞 K) K)} (ha : AdelicLevel.glFin (𝓞 K) K a = 1)
    (z : GL (Fin 2) (v.adicCompletion K)) : ι (𝓞 K) K v z * a = a * ι (𝓞 K) K v z := by
  refine adelicGL_ext (𝓞 K) K ?_ ?_
  · rw [map_mul, map_mul, glArch_ι, one_mul, mul_one]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

private theorem conj_invariant_comb {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y)
    {J : Type*} (s : Finset J) (c : J → ℂ) (h : J → GL (Fin 2) (v.adicCompletion K))
    (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    (∑ j ∈ s, c j * f ((ι (𝓞 K) K v (h j))⁻¹ * (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹)))
      = ∑ j ∈ s, c j * f ((ι (𝓞 K) K v (h j))⁻¹ * y) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hc : (ι (𝓞 K) K v (h j))⁻¹ * rowIsometryInclAt₀ K w k = rowIsometryInclAt₀ K w k * (ι (𝓞 K) K v (h j))⁻¹ := by
    rw [← map_inv]
    exact ι_mul_comm_of_glFin_eq_one (glFin_rowIsometryInclAt₀ K w k) _
  rw [← hfK w k ((ι (𝓞 K) K v (h j))⁻¹ * y)]
  congr 1
  rw [← mul_assoc, ← mul_assoc, hc, mul_assoc _ _ y]

private theorem rightConv_comb (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) {J : Type*} (s : Finset J) (c : J → ℂ) (h : J → GL (Fin 2) (v.adicCompletion K))
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ (fun x => ∑ j ∈ s, c j * f ((ι (𝓞 K) K v (h j))⁻¹ * x)) g
      = ∑ j ∈ s, c j * rightConv K φ f (g * ι (𝓞 K) K v (h j)) := by
  letI : MeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hterm : ∀ j ∈ s, rightConv K φ f (g * ι (𝓞 K) K v (h j))
      = rightConv K φ (fun y => f ((ι (𝓞 K) K v (h j))⁻¹ * y)) g :=
    fun j _ => rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply K φ f g _
  rw [Finset.sum_congr rfl fun j hj => by rw [hterm j hj]]
  simp only [rightConv_apply]
  have hint : ∀ j ∈ s, Integrable (fun x => c j * (φ (g * x) * f ((ι (𝓞 K) K v (h j))⁻¹ * x)))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro j _
    have hcont : Continuous fun x => φ (g * x) * f ((ι (𝓞 K) K v (h j))⁻¹ * x) :=
      (hφ.comp (continuous_const.mul continuous_id)).mul (hfc.comp (continuous_const.mul continuous_id))
    have hsupp : HasCompactSupport fun x => f ((ι (𝓞 K) K v (h j))⁻¹ * x) :=
      hfs.comp_homeomorph (Homeomorph.mulLeft (ι (𝓞 K) K v (h j))⁻¹)
    exact (hcont.integrable_of_hasCompactSupport hsupp.mul_left).const_mul (c j)
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum s hint]
  congr 1
  funext x
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end Combination
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

end OrbitCombination
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm AutomorphicForm.SmoothCusp
open NumberField.AdelicLevel HeckeIntegralSeam AdelicDock

namespace LevelLowering

open PlaceEmbedding LevelComponents

section IdealBoundAtOtherPlaces

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

private theorem not_dvd_asIdeal_of_ne {v w : HeightOneSpectrum R} (hwv : w ≠ v) : ¬ w.asIdeal ∣ v.asIdeal := by
  intro h
  exact hwv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.le_of_dvd h)).symm)

private theorem idealBound_mul_pow_of_ne {M : Ideal R} (hM : M ≠ ⊥) {v w : HeightOneSpectrum R} (hwv : w ≠ v) (k : ℕ) :
    idealBound R (M * v.asIdeal ^ k) w = idealBound R M w := by
  classical
  have hv : v.asIdeal ^ k ≠ ⊥ := pow_ne_zero k v.ne_bot
  have hMv : M * v.asIdeal ^ k ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hM hv
  rw [idealBound_of_ne_bot hMv, idealBound_of_ne_bot hM, ← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.mpr hM) (Associates.mk_ne_zero.mpr hv) w.associates_irreducible]
  have h0 : (Associates.mk w.asIdeal).count (Associates.mk (v.asIdeal ^ k)).factors = 0 := by
    by_contra h
    exact not_dvd_asIdeal_of_ne hwv
      (w.prime.dvd_of_dvd_pow ((Associates.count_ne_zero_iff_dvd hv w.irreducible).mp h))
  rw [h0, add_zero]

end IdealBoundAtOtherPlaces
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section Local

variable {F : Type} [Field F] [NumberField F]

private theorem isLocalLevelOne_mul_pow_iff
    {M : Ideal (𝓞 F)} (hM : M ≠ ⊥) {v w : HeightOneSpectrum (𝓞 F)} (hwv : w ≠ v)
    (k : ℕ) (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) :
    IsLocalLevelOne (𝓞 F) F w (M * v.asIdeal ^ k) m ↔ IsLocalLevelOne (𝓞 F) F w M m := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [idealBound_mul_pow_of_ne hM hwv] at h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩ <;> rw [idealBound_mul_pow_of_ne hM hwv] <;> assumption

private theorem mem_localLevelOne_mul_pow_iff
    {M : Ideal (𝓞 F)} (hM : M ≠ ⊥) {v w : HeightOneSpectrum (𝓞 F)} (hwv : w ≠ v)
    (k : ℕ) (z : GL (Fin 2) (w.adicCompletion F)) :
    z ∈ localLevelOne (𝓞 F) F w (M * v.asIdeal ^ k) ↔ z ∈ localLevelOne (𝓞 F) F w M := by
  rw [mem_localLevelOne_iff, mem_localLevelOne_iff, isLocalLevelOne_mul_pow_iff hM hwv,
    isLocalLevelOne_mul_pow_iff hM hwv]

end Local
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section AwayFromPlace

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private def LocalAnti : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 F)) {M N : Ideal (𝓞 F)}, M ∣ N → N ≠ ⊥ →
    localLevelOne (𝓞 F) F w N ≤ localLevelOne (𝓞 F) F w M

variable {v}

private theorem glArch_awayFrom_eq_one {p : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hp : p ∈ finiteAdelicGL2Subgroup F) :
    glArch (𝓞 F) F (awayFrom (𝓞 F) F v p) = 1 := by
  rw [glArch_awayFrom]
  exact (mem_finiteAdelicGL2Subgroup_iff F p).mp hp

private theorem finComponent_awayFrom_self (p : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (awayFrom (𝓞 F) F v p)) = 1 :=
  compAt_awayFrom (𝓞 F) F v p

private theorem awayFrom_mem_levelOne_inf {N M : Ideal (𝓞 F)} (hanti : LocalAnti (F := F)) (hMN : M ∣ N) (hN : N ≠ ⊥)
    {p : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hp : p ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    awayFrom (𝓞 F) F v p ∈ levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨-, hcomp⟩ := components_of_mem_U F hp
  refine mem_U_of_components F (glArch_awayFrom_eq_one (Subgroup.mem_inf.mp hp).2) fun w => ?_
  by_cases hwv : w = v
  · subst hwv
    rw [finComponent_awayFrom_self]
    exact one_mem _
  · rw [finComponent_glFin_awayFrom_of_ne (𝓞 F) F v p hwv]
    exact hanti w hMN hN (hcomp w)

private theorem awayFrom_mem_principalLevel_mul_pow_inf {N M : Ideal (𝓞 F)} (hanti : LocalAnti (F := F)) (hMN : M ∣ N)
    (hN : N ≠ ⊥) (hM : M ≠ ⊥) (k : ℕ) {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    awayFrom (𝓞 F) F v p ∈ principalLevel (𝓞 F) F (M * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup F := by
  have hpU : p ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := P_le_U F N hp
  obtain ⟨-, hcomp⟩ := components_of_mem_U F hpU
  have hU : awayFrom (𝓞 F) F v p ∈ levelOne (𝓞 F) F (M * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F (glArch_awayFrom_eq_one (Subgroup.mem_inf.mp hpU).2) fun w => ?_
    by_cases hwv : w = v
    · subst hwv
      rw [finComponent_awayFrom_self]
      exact one_mem _
    · rw [finComponent_glFin_awayFrom_of_ne (𝓞 F) F v p hwv, mem_localLevelOne_mul_pow_iff hM hwv]
      exact hanti w hMN hN (hcomp w)
  refine mem_P_of_components F hU fun w => ?_
  by_cases hwv : w = v
  · subst hwv
    rw [finComponent_awayFrom_self, mul_one, inv_mul_cancel]
    exact one_mem _
  · rw [finComponent_glFin_awayFrom_of_ne (𝓞 F) F v p hwv, mem_localLevelOne_mul_pow_iff hM hwv]
    exact hanti w hMN hN (components_of_mem_P F hp w)

private theorem awayFrom_mem_U {D E₀ N : Ideal (𝓞 F)} (k : ℕ) (hanti : LocalAnti (F := F)) (hD : D ∣ N) (hE : E₀ ∣ N)
    (hN : N ≠ ⊥) (hE₀ : E₀ ≠ ⊥) {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    awayFrom (𝓞 F) F v p
      ∈ levelOne (𝓞 F) F D ⊓ principalLevel (𝓞 F) F (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup F := by
  have h1 := awayFrom_mem_levelOne_inf (v := v) hanti hD hN (P_le_U F N hp)
  have h2 := awayFrom_mem_principalLevel_mul_pow_inf (v := v) hanti hE hN hE₀ k hp
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h1).1, (Subgroup.mem_inf.mp h2).1⟩,
    (Subgroup.mem_inf.mp h1).2⟩

end AwayFromPlace
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section LowerGroup

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem compAt_mem_localLevelOne_pow (hanti : LocalAnti (F := F)) {D E₀ : Ideal (𝓞 F)} (c : ℕ)
    (hDv : D * v.asIdeal ^ c ≠ ⊥) {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ levelOne (𝓞 F) F (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 F) F E₀ ⊓ finiteAdelicGL2Subgroup F) :
    compAt (𝓞 F) F v p ∈ localLevelOne (𝓞 F) F v (v.asIdeal ^ c) := by
  have hpU : p ∈ levelOne (𝓞 F) F (D * v.asIdeal ^ c) ⊓ finiteAdelicGL2Subgroup F :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hp).1).1, (Subgroup.mem_inf.mp hp).2⟩
  rw [compAt_apply]
  exact hanti v (dvd_mul_left _ _) hDv ((components_of_mem_U F hpU).2 v)

private theorem awayFrom_mem_U_of_mem_outputGroup (hanti : LocalAnti (F := F)) {D E₀ : Ideal (𝓞 F)} (c k : ℕ)
    (hDv : D * v.asIdeal ^ c ≠ ⊥) (hE₀ : E₀ ≠ ⊥) {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ levelOne (𝓞 F) F (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 F) F E₀ ⊓ finiteAdelicGL2Subgroup F) :
    awayFrom (𝓞 F) F v p
      ∈ levelOne (𝓞 F) F D ⊓ principalLevel (𝓞 F) F (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup F := by
  have hfin : p ∈ finiteAdelicGL2Subgroup F := (Subgroup.mem_inf.mp hp).2
  have hpU : p ∈ levelOne (𝓞 F) F (D * v.asIdeal ^ c) ⊓ finiteAdelicGL2Subgroup F :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hp).1).1, hfin⟩
  have hpP : p ∈ principalLevel (𝓞 F) F E₀ ⊓ finiteAdelicGL2Subgroup F :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hp).1).2, hfin⟩
  have h1 := awayFrom_mem_levelOne_inf (v := v) hanti (dvd_mul_right D _) hDv hpU
  have h2 := awayFrom_mem_principalLevel_mul_pow_inf (v := v) hanti (dvd_refl E₀) hE₀ hE₀ k hpP
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h1).1, (Subgroup.mem_inf.mp h2).1⟩,
    (Subgroup.mem_inf.mp h1).2⟩

end LowerGroup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section Invariance

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem invariant_outputGroup (hanti : LocalAnti (F := F)) {D E₀ : Ideal (𝓞 F)} (c k : ℕ)
    (hDv : D * v.asIdeal ^ c ≠ ⊥) (hE₀ : E₀ ≠ ⊥) {y : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hyv : ∀ z ∈ localLevelOne (𝓞 F) F v (v.asIdeal ^ c), ∀ g, y (g * ι (𝓞 F) F v z) = y g)
    (hyaway : ∀ q ∈ levelOne (𝓞 F) F D ⊓ principalLevel (𝓞 F) F (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup F,
      compAt (𝓞 F) F v q = 1 → ∀ g, y (g * q) = y g)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ levelOne (𝓞 F) F (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 F) F E₀ ⊓ finiteAdelicGL2Subgroup F) :
    y (g * p) = y g := by
  conv_lhs => rw [← awayFrom_mul_ι_compAt (𝓞 F) F v p]
  rw [← mul_assoc, hyv _ (compAt_mem_localLevelOne_pow hanti c hDv hp),
    hyaway _ (awayFrom_mem_U_of_mem_outputGroup hanti c k hDv hE₀ hp) (compAt_awayFrom (𝓞 F) F v p)]

end Invariance
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

section HeckeTransfer

variable {F : Type} [Field F] [NumberField F]

private theorem isHeckeCosetEigenfunctionAt_of_common_system {Ud Us : Subgroup (AdelicGL2 (𝓞 F) F)}
    {gv : AdelicGL2 (𝓞 F) F} {w : HeightOneSpectrum (𝓞 F)} {y : AdelicGL2 (𝓞 F) F → ℂ} {a : ℂ}
    (hyd : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ Ud, y (g * u) = y g)
    (hy : IsHeckeCosetEigenfunctionAt F Ud gv w y a)
    {reps : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 F) F}
    (hd : IsHeckeCosetSystem Ud gv reps) (hs : IsHeckeCosetSystem Us gv reps) :
    IsHeckeCosetEigenfunctionAt F Us gv w y a := by
  obtain ⟨reps₀, h₀, heq⟩ := hy
  refine ⟨reps, hs, fun g => ?_⟩
  have h := heq g
  unfold heckeCosetSum at h ⊢
  rw [heckeCosetSum_eq_of_isHeckeCosetSystem h₀ hd hyd g]
  exact h

private theorem isIsotypicCuspFormAt_of_level {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {Nd Ns : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Φ : HeckeEigensystem F ℂ} {y : AdelicGL2 (𝓞 F) F → ℂ}
    (hy : IsIsotypicCuspFormAt F pins ξ Nd S Φ y)
    (hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U Ns, y (g * u) = y g)
    (hhecke : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      IsHeckeCosetEigenfunctionAt F (pins.U Ns) (pins.gen w) w y (Φ.a w)) :
    IsIsotypicCuspFormAt F pins ξ Ns S Φ y :=
  ⟨hy.smoothCusp, hy.continuous, hlev, hhecke, hy.central_eigen⟩

end HeckeTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

end LevelLowering
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

namespace InfinitelyManyPlaces

open NumberField IsDedekindDomain

private theorem exists_isMaximal_comap_eq_span (K : Type) [Field K] [NumberField K] (p : Nat.Primes) :
    ∃ Q : Ideal (𝓞 K), Q.IsMaximal ∧ Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
  have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
  haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  refine Ideal.exists_ideal_over_maximal_of_isIntegral _ ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
  exact bot_le

private noncomputable def placeAbove (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : HeightOneSpectrum (𝓞 K) :=
  ⟨(exists_isMaximal_comap_eq_span K p).choose, (exists_isMaximal_comap_eq_span K p).choose_spec.1.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField (exists_isMaximal_comap_eq_span K p).choose_spec.1
      (RingOfIntegers.not_isField K)⟩

private theorem placeAbove_injective (K : Type) [Field K] [NumberField K] : Function.Injective (placeAbove K) := by
  intro p q hpq
  have h : (placeAbove K p).asIdeal = (placeAbove K q).asIdeal := by rw [hpq]
  have hc : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← (exists_isMaximal_comap_eq_span K p).choose_spec.2, ← (exists_isMaximal_comap_eq_span K q).choose_spec.2]
    exact congrArg (Ideal.comap (algebraMap ℤ (𝓞 K))) h
  have ha : Associated ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := Ideal.span_singleton_eq_span_singleton.mp hc
  have hn : (p : ℕ) = (q : ℕ) := by
    have h' := Int.associated_iff_natAbs.mp ha
    rwa [Int.natAbs_natCast, Int.natAbs_natCast] at h'
  exact Subtype.ext hn

private theorem infinite_heightOneSpectrum
    (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
  exact Infinite.of_injective _ (placeAbove_injective K)

end InfinitelyManyPlaces
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

namespace LevelAspect

open PlaceEmbedding

variable {K : Type} [Field K] [NumberField K]

private theorem _root_.LevelAspect.infinite_heightOneSpectrum : Infinite (HeightOneSpectrum (𝓞 K)) :=
  InfinitelyManyPlaces.infinite_heightOneSpectrum K

p2m_export "LevelAspect" "infinite_heightOneSpectrum"
private theorem _root_.LevelAspect.isKfSmooth_rightConv (u f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    IsKfSmooth K (rightConv K u f) :=
  SmoothConvolution.isKfSmooth_rightConv u f hf

p2m_export "LevelAspect" "isKfSmooth_rightConv"
open scoped Classical in
private theorem comb_testFn (S : Finset (HeightOneSpectrum (𝓞 K))) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsUnitFactorizableAt K ⊥ S f)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (s : Finset (GL (Fin 2) (v.adicCompletion K))) (c : GL (Fin 2) (v.adicCompletion K) → ℂ) :
    IsUnitFactorizableAt K ⊥ S (fun x => ∑ h ∈ s, c h * f ((ι (𝓞 K) K v h)⁻¹ * x)) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        (∑ h ∈ s, c h * f ((ι (𝓞 K) K v h)⁻¹ * (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹)))
          = ∑ h ∈ s, c h * f ((ι (𝓞 K) K v h)⁻¹ * y)) ∧
      ∀ g : AdelicGL2 (𝓞 K) K, rightConv K φ (fun x => ∑ h ∈ s, c h * f ((ι (𝓞 K) K v h)⁻¹ * x)) g
        = ∑ h ∈ s, c h * rightConv K φ f (g * ι (𝓞 K) K v h) :=
  ⟨OrbitCombination.isUnitFactorizableAt_comb hv hf s c (fun j => j),
    fun w k y => OrbitCombination.conj_invariant_comb hfK s c (fun j => j) w k y,
    fun g => OrbitCombination.rightConv_comb φ f hφ
      (IsotypicConvolution.continuous_of_isFactorizableTestFn hf.isFactorizableTestFn)
      (IsotypicConvolution.hasCompactSupport_of_isFactorizableTestFn hf.isFactorizableTestFn) s c (fun j => j) g⟩

private theorem cong_compAt_of_mem_principalLevel {v : HeightOneSpectrum (𝓞 K)} {N : Ideal (𝓞 K)} {M : ℕ}
    (hN : v.asIdeal ^ M ∣ N) (hN0 : N ≠ ⊥) {p : AdelicGL2 (𝓞 K) K}
    (hp : p ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    LocalOrbit.Cong v M (compAt (𝓞 K) K v p) := by
  intro i j
  have h1 := (LevelComponents.components_of_mem_U K (LevelComponents.P_le_U K N hp)).2 v
  have h2 := LevelComponents.components_of_mem_P K hp v
  exact (LocalOrbit.entries_of_levelOne_of_conj v h1 h2 i j).trans (LocalOrbit.idealBound_anti v hN hN0)

private theorem localAnti : LevelLowering.LocalAnti (F := K) :=
  fun w _ _ hMN hN => LocalOrbit.localLevelOne_anti w hMN hN

private theorem _root_.LevelAspect.awayFrom_mem_U {v : HeightOneSpectrum (𝓞 K)} {D E₀ N : Ideal (𝓞 K)} {k : ℕ} (hD : D ∣ N) (hE₀ : E₀ ∣ N)
    (hN0 : N ≠ ⊥) (hE₀0 : E₀ ≠ ⊥) {p : AdelicGL2 (𝓞 K) K}
    (hp : p ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    awayFrom (𝓞 K) K v p ∈
      levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K :=
  LevelLowering.awayFrom_mem_U k localAnti hD hE₀ hN0 hE₀0 hp

p2m_export "LevelAspect" "awayFrom_mem_U"
private theorem relevel (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ) (Nd Ns : Ideal (𝓞 K))
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hdeep : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ Nd S π y)
    (hinv : ∀ g : AdelicGL2 (𝓞 K) K, ∀ p ∈ principalLevel (𝓞 K) K Ns ⊓ finiteAdelicGL2Subgroup K, y (g * p) = y g)
    (hsys : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
      ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → GL (Fin 2) (w.adicCompletion K),
        HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K Nd ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K w) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) ∧
          HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K Ns ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K w) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i)))) :
    IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ Ns S π y :=
  LevelLowering.isIsotypicCuspFormAt_of_level hdeep (fun g u hu => hinv g u hu) fun w hw => by
    obtain ⟨r, hd, hs⟩ := hsys w hw
    exact LevelLowering.isHeckeCosetEigenfunctionAt_of_common_system hdeep.level_invariant (hdeep.hecke_eigen w hw)
      hd hs

private theorem hsys_principal_pair {w : HeightOneSpectrum (𝓞 K)} {N₁ N₂ : Ideal (𝓞 K)} (h₁ : ¬ w.asIdeal ∣ N₁)
    (h₂ : ¬ w.asIdeal ∣ N₂) :
    ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → GL (Fin 2) (w.adicCompletion K),
      HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N₁ ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K w) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) ∧
        HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N₂ ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K w) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) := by
  obtain ⟨ϖ, hϖ0, -, hgen, sec, -, hM⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K w
  have habs : Ideal.absNorm w.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero w.ne_bot)
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := (Ideal.absNorm_ne_zero_iff w.asIdeal).mp habs
  haveI : Fintype (𝓞 K ⧸ w.asIdeal) := Fintype.ofFinite _
  let e := (Fintype.equivFinOfCardEq (LevelComponents.card_option_quotient K w)).symm
  have key : ∀ {N : Ideal (𝓞 K)}, ¬ w.asIdeal ∣ N →
      HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K w)
        ((fun i : Option (𝓞 K ⧸ w.asIdeal) => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w
          (i.elim (LocalGL2.localRepInf ϖ hϖ0)
            (fun c => LocalGL2.localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (w.adicCompletionIntegers K) (sec c)))))) ∘
          e) := by
    intro N hN
    have H := hM N hN
    rw [← hgen] at H
    have S := LevelComponents.isHeckeCosetSystem_principal_of_not_dvd K w hN (LocalGL2.diagPi ϖ hϖ0)
      (fun i : Option (𝓞 K ⧸ w.asIdeal) => i.elim (LocalGL2.localRepInf ϖ hϖ0)
        (fun c => LocalGL2.localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (w.adicCompletionIntegers K) (sec c)))) H
    rw [hgen] at S
    exact LevelComponents.reindex S e
  exact ⟨(fun i : Option (𝓞 K ⧸ w.asIdeal) => i.elim (LocalGL2.localRepInf ϖ hϖ0)
      (fun c => LocalGL2.localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (w.adicCompletionIntegers K) (sec c)))) ∘ e,
    key h₁, key h₂⟩

private theorem _root_.LevelAspect.invariant_outputGroup {v : HeightOneSpectrum (𝓞 K)} {D E₀ : Ideal (𝓞 K)} (c k : ℕ)
    (hDv : D * v.asIdeal ^ c ≠ ⊥) (hE₀ : E₀ ≠ ⊥) {y : AdelicGL2 (𝓞 K) K → ℂ}
    (hyv : ∀ z ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c), ∀ g, y (g * ι (𝓞 K) K v z) = y g)
    (hyaway : ∀ q ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
      compAt (𝓞 K) K v q = 1 → ∀ g, y (g * q) = y g)
    (g : AdelicGL2 (𝓞 K) K) {p : AdelicGL2 (𝓞 K) K}
    (hp : p ∈ levelOne (𝓞 K) K (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 K) K E₀ ⊓ finiteAdelicGL2Subgroup K) :
    y (g * p) = y g :=
  LevelLowering.invariant_outputGroup localAnti c k hDv hE₀ hyv hyaway g hp

p2m_export "LevelAspect" "invariant_outputGroup"
private theorem exists_depth (v : HeightOneSpectrum (𝓞 K)) {A B : Ideal (𝓞 K)} (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    ∃ M : ℕ, 1 ≤ M ∧ WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) A v ∧
      WithZero.exp (-(M : ℤ)) ≤ AdelicLevel.idealBound (𝓞 K) B v := by
  obtain ⟨a, ha⟩ := LocalOrbit.exists_exp_neg_le_idealBound v hA
  obtain ⟨b, hb⟩ := LocalOrbit.exists_exp_neg_le_idealBound v hB
  refine ⟨max 1 (max a b), le_max_left _ _, le_trans ?_ ha, le_trans ?_ hb⟩ <;>
    (rw [WithZero.exp_le_exp]; push_cast; omega)

private theorem exists_entry_bound_finset (v : HeightOneSpectrum (𝓞 K))
    (s : Finset (GL (Fin 2) (v.adicCompletion K))) :
    ∃ n : ℕ, ∀ h ∈ s,
      (∀ i j, Valued.v ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (n : ℤ)) ∧
      ∀ i j, Valued.v (((h⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
        ≤ WithZero.exp (n : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun h hh => absurd hh (Finset.notMem_empty h)⟩
  | insert a s _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨na, hna, hna'⟩ := LocalOrbit.exists_entry_bound v a
    have hmono : ∀ {m m' : ℕ}, m ≤ m' → (WithZero.exp (m : ℤ) : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (m' : ℤ) :=
      fun hmm => by rw [WithZero.exp_le_exp]; exact_mod_cast hmm
    refine ⟨max n na, fun h hh => ?_⟩
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact ⟨fun i j => (hna i j).trans (hmono (le_max_right _ _)),
        fun i j => (hna' i j).trans (hmono (le_max_right _ _))⟩
    · exact ⟨fun i j => ((hn h hh).1 i j).trans (hmono (le_max_left _ _)),
        fun i j => ((hn h hh).2 i j).trans (hmono (le_max_left _ _))⟩

end LevelAspect
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero.LocalOrbit"

open LevelAspect LocalOrbit PlaceEmbedding in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (D E₀ : Ideal (𝓞 K)) (k : ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (D * E₀ * v.asIdeal ^ k) S π φ)
    (hφD : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        φ (g * x) = φ g)
    (hφt : φ ∈ archCutSubmodule K tys) (hφ0 : φ ≠ 0) :
    ∃ (c : ℕ) (φ' : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ (D * v.asIdeal ^ c * E₀) S π φ' ∧
      (∀ g : AdelicGL2 (𝓞 K) K,
        ∀ x ∈ levelOne (𝓞 K) K (D * v.asIdeal ^ c) ⊓ principalLevel (𝓞 K) K E₀ ⊓ finiteAdelicGL2Subgroup K,
          φ' (g * x) = φ' g) ∧
      φ' ∈ archCutSubmodule K tys ∧ φ' ≠ 0 := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

  have hS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ D * E₀ * v.asIdeal ^ k → w ∈ S := by
    intro w hw
    by_contra hwS
    have hbot := AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd K w _ _ ξ
      (D * E₀ * v.asIdeal ^ k) S π hwS hw
    have hmem := hφ.mem_isotypicCuspSubmodule
    rw [hbot, Submodule.mem_bot] at hmem
    exact hφ0 hmem
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := infinite_heightOneSpectrum
  have hlev0 : D * E₀ * v.asIdeal ^ k ≠ ⊥ := by
    intro h0
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset S
    exact hw (hS w (by rw [h0]; exact dvd_zero _))
  have hD0 : D ≠ ⊥ := fun h => hlev0 (by rw [h, Submodule.bot_mul, Submodule.bot_mul])
  have hE₀0 : E₀ ≠ ⊥ := fun h => hlev0 (by rw [h, Submodule.mul_bot, Submodule.bot_mul])
  have hB0 : E₀ * v.asIdeal ^ k ≠ ⊥ := mul_ne_zero hE₀0 (pow_ne_zero k v.ne_bot)

  have hφc : Continuous φ := hφ.continuous
  obtain ⟨f₀, hf₀, hf₀L, hf₀K, hΦ0⟩ :=
    AutomorphicForm.exists_isUnitFactorizableAt_rightConv_ne_zero K cK uK d₁K d₂K TK ξ S π v D E₀ k φ hφ hφD hφ0
  have hff₀ : IsFactorizableTestFn K f₀ := hf₀.isFactorizableTestFn
  have hΦc : Continuous (rightConv K φ f₀) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn K φ hφc f₀ hff₀).1

  have hΦU : ∀ t ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
      ∀ x, rightConv K φ f₀ (x * t) = rightConv K φ f₀ x := by
    intro t ht x
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply K φ f₀ x t]
    simp only [hf₀L t⁻¹ (Subgroup.inv_mem _ ht)]

  obtain ⟨M, hM1, hMD, hMB⟩ := exists_depth v hD0 hB0
  have hΦcong : ∀ g : GL (Fin 2) (v.adicCompletion K), Cong v M g →
      ∀ x, rightConv K φ f₀ (x * ι (𝓞 K) K v g) = rightConv K φ f₀ x :=
    fun g hg x => hΦU _ (ι_mem_level_of_cong v hM1 hMD hMB hg) x
  have hsmoothW := orbitRep_smooth v (rightConv K φ f₀) hΦcong
  have hSgen : ∀ m : ℕ, ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ¬ w.asIdeal ∣ D * E₀ * v.asIdeal ^ m := by
    intro m w hwS hw
    have hwv : w ≠ v := fun h => hwS (h ▸ hv)
    rcases w.prime.dvd_or_dvd hw with hw1 | hw2
    · exact hwS (hS w (dvd_mul_of_dvd_left hw1 _))
    · exact hwv (HeightOneSpectrum.ext
        (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.le_of_dvd (w.prime.dvd_of_dvd_pow hw2))).symm)

  have hcomb : ∀ w : orbitSpan v (rightConv K φ f₀), ∃ (s : Finset (GL (Fin 2) (v.adicCompletion K)))
      (cw : GL (Fin 2) (v.adicCompletion K) → ℂ),
      IsUnitFactorizableAt K ⊥ S (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) ∧
      (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion) (y : AdelicGL2 (𝓞 K) K),
        (∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ *
          (rowIsometryInclAt₀ K w' k * y * (rowIsometryInclAt₀ K w' k)⁻¹)))
          = ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * y)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, rightConv K φ (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) g
        = ∑ h ∈ s, cw h * rightConv K φ f₀ (g * ι (𝓞 K) K v h)) ∧
      (w : AdelicGL2 (𝓞 K) K → ℂ) = rightConv K φ (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) := by
    intro w
    have hw2 : (w : AdelicGL2 (𝓞 K) K → ℂ) ∈ Submodule.span ℂ (Set.range (orbitGen v (rightConv K φ f₀))) := w.2
    obtain ⟨cf, hcf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hw2
    obtain ⟨hfy, hfyK, hfyconv⟩ := comb_testFn S hv hf₀ hf₀K φ hφc cf.support (fun h => cf h)
    refine ⟨cf.support, fun h => cf h, hfy, hfyK, hfyconv, ?_⟩
    funext g
    rw [hfyconv g, ← hcf, Finsupp.sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbitGen_apply]

  have hdeepIso : ∀ (s : Finset (GL (Fin 2) (v.adicCompletion K))) (cw : GL (Fin 2) (v.adicCompletion K) → ℂ),
      IsUnitFactorizableAt K ⊥ S (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) →
      (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion) (y : AdelicGL2 (𝓞 K) K),
        (∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ *
          (rowIsometryInclAt₀ K w' k * y * (rowIsometryInclAt₀ K w' k)⁻¹)))
          = ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * y)) →
      ∃ n : ℕ, IsIsotypicCuspFormAt K
          (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
            (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξ (D * E₀ * v.asIdeal ^ (M + 2 * n)) S π
          (rightConv K φ (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x))) ∧
        rightConv K φ (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) ∈
          archCutSubmodule K tys := by
    intro s cw hfs hfsK
    obtain ⟨n, hn⟩ := exists_entry_bound_finset v s
    have hdeep : ∀ p ∈ principalLevel (𝓞 K) K (D * E₀ * v.asIdeal ^ (M + 2 * n)) ⊓ finiteAdelicGL2Subgroup K,
        ∀ g, (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) (p * g)
          = (fun x => ∑ h ∈ s, cw h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) g := by
      intro p hp g
      simp only
      refine Finset.sum_congr rfl fun h hh => ?_
      congr 1

      have hND : D ∣ D * E₀ * v.asIdeal ^ (M + 2 * n) := ⟨E₀ * v.asIdeal ^ (M + 2 * n), by ring⟩
      have hNE : E₀ ∣ D * E₀ * v.asIdeal ^ (M + 2 * n) := ⟨D * v.asIdeal ^ (M + 2 * n), by ring⟩
      have hNv : v.asIdeal ^ (M + 2 * n) ∣ D * E₀ * v.asIdeal ^ (M + 2 * n) := ⟨D * E₀, by ring⟩
      have hN0 : D * E₀ * v.asIdeal ^ (M + 2 * n) ≠ ⊥ := mul_ne_zero (mul_ne_zero hD0 hE₀0) (pow_ne_zero _ v.ne_bot)
      have haway := awayFrom_mem_U (v := v) (k := k) hND hNE hN0 hE₀0 hp
      have hcongp := cong_compAt_of_mem_principalLevel hNv hN0 hp
      have hloc : ι (𝓞 K) K v (h⁻¹ * compAt (𝓞 K) K v p * h) ∈ levelOne (𝓞 K) K D ⊓
          principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K :=
        ι_mem_level_of_cong v hM1 hMD hMB (cong_conj v (hn h hh).1 (hn h hh).2 hcongp)
      have hsplit : (ι (𝓞 K) K v h)⁻¹ * (p * g) =
          awayFrom (𝓞 K) K v p * (ι (𝓞 K) K v (h⁻¹ * compAt (𝓞 K) K v p * h) *
            ((ι (𝓞 K) K v h)⁻¹ * g)) := by
        conv_lhs => rw [← awayFrom_mul_ι_compAt (𝓞 K) K v p]
        rw [map_mul, map_mul, map_inv]
        have hc := ι_mul_awayFrom_comm (𝓞 K) K v p h⁻¹
        rw [map_inv] at hc
        simp only [← mul_assoc]
        rw [hc]
        simp only [mul_assoc, mul_inv_cancel_left]
      rw [hsplit, hf₀L _ haway, hf₀L _ hloc]
    have hS' := hSgen (M + 2 * n)
    have hsysP : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
        ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → GL (Fin 2) (w.adicCompletion K),
          HeckeIntegralSeam.IsHeckeCosetSystem
              (principalLevel (𝓞 K) K (D * E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K w)
              (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) ∧
            HeckeIntegralSeam.IsHeckeCosetSystem
              ((fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (D * E₀ * v.asIdeal ^ (M + 2 * n)))
              (heckeGen (𝓞 K) K w) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) :=
      fun w hwS => hsys_principal_pair (fun hw => hwS (hS w hw)) (hS' w hwS)
    obtain ⟨hIso, hcut⟩ :=
      AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt K cK
        uK d₁K d₂K TK hcK hd₁K hdK hcovK (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) ξ
        (D * E₀ * v.asIdeal ^ k) (D * E₀ * v.asIdeal ^ (M + 2 * n)) S hS π φ hφ hsysP _ hfs hdeep hfsK
    exact ⟨n, hIso, hcut tys hφt⟩

  have hslW : ∀ w : orbitSpan v (rightConv K φ f₀),
      (∀ h : GL (Fin 2) (v.adicCompletion K), (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 →
        orbitRep v (rightConv K φ f₀) h w = w) → w = 0 := by
    intro w hfixw
    obtain ⟨s, cw, hfw, hfwK, -, hwconv⟩ := hcomb w
    obtain ⟨n, hwIso, -⟩ := hdeepIso s cw hfw hfwK
    have hfix : ∀ t : GL (Fin 2) (v.adicCompletion K), (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 →
        ∀ y : AdelicGL2 (𝓞 K) K, (w : AdelicGL2 (𝓞 K) K → ℂ)
          (y * AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v t)) = (w : AdelicGL2 (𝓞 K) K → ℂ) y := by
      intro t ht y
      have h1 := congrArg (fun u : orbitSpan v (rightConv K φ f₀) => (u : AdelicGL2 (𝓞 K) K → ℂ) y) (hfixw t ht)
      first | exact h1 | simpa using h1
    rw [hwconv] at hfix
    have hzero := AutomorphicForm.eq_zero_of_mem_isotypicCuspSubmodule_of_forall_det_eq_one_invariant K
      cK uK d₁K d₂K TK ξ
      (D * E₀ * v.asIdeal ^ (M + 2 * n)) S π v _ hwIso.mem_isotypicCuspSubmodule hfix
    rw [← hwconv] at hzero
    exact Submodule.coe_eq_zero.mp hzero
  have hWne : ∃ w : orbitSpan v (rightConv K φ f₀), w ≠ 0 :=
    ⟨⟨rightConv K φ f₀, self_mem_orbitSpan v _⟩, fun h => hΦ0 (by simpa using congrArg Subtype.val h)⟩

  obtain ⟨c₀, y, hy0, hyfix₀⟩ :=
    AutomorphicForm.exists_ne_zero_forall_mem_localLevelOne_smul_eq_of_smooth_of_det_one_invariant_eq_zero K v _
      (orbitRep v (rightConv K φ f₀)) hWne
    (fun w => by obtain ⟨m, hm⟩ := hsmoothW w; exact ⟨m, fun g hg => hm g hg⟩) hslW
  have hc1 : 1 ≤ c₀ + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hyfix : ∀ g ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ (c₀ + 1)),
      orbitRep v (rightConv K φ f₀) g y = y :=
    fun g hg => hyfix₀ g (localLevelOne_anti v (pow_dvd_pow v.asIdeal (Nat.le_succ c₀)) (pow_ne_zero _ v.ne_bot) hg)

  obtain ⟨sy, cy, hfy, hfyK, hyconv, hyfun⟩ := hcomb y
  have hy0' : rightConv K φ (fun x => ∑ h ∈ sy, cy h * f₀ ((ι (𝓞 K) K v h)⁻¹ * x)) ≠ 0 := by
    rw [← hyfun]
    exact fun h0 => hy0 (Submodule.coe_eq_zero.mp h0)

  obtain ⟨n, hyIso, hycutm⟩ := hdeepIso sy cy hfy hfyK

  have hyv : ∀ g ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ (c₀ + 1)), ∀ z,
      (y : AdelicGL2 (𝓞 K) K → ℂ) (z * ι (𝓞 K) K v g) = (y : AdelicGL2 (𝓞 K) K → ℂ) z := by
    intro g hg z
    have := congrArg (fun w : orbitSpan v (rightConv K φ f₀) => (w : AdelicGL2 (𝓞 K) K → ℂ) z) (hyfix g hg)
    simpa using this
  have hyaway : ∀ p ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
      compAt (𝓞 K) K v p = 1 → ∀ z, (y : AdelicGL2 (𝓞 K) K → ℂ) (z * p) = (y : AdelicGL2 (𝓞 K) K → ℂ) z := by
    intro p hp hp1 z
    rw [hyfun, hyconv, hyconv]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc, ← ι_mul_comm_of_compAt_eq_one (𝓞 K) K v hp1 h, ← mul_assoc, hΦU p hp]
  have hinv : ∀ (N : Ideal (𝓞 K)), D ∣ N → E₀ ∣ N → v.asIdeal ^ (c₀ + 1) ∣ N → N ≠ ⊥ →
      ∀ z, ∀ p ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        (y : AdelicGL2 (𝓞 K) K → ℂ) (z * p) = (y : AdelicGL2 (𝓞 K) K → ℂ) z := by
    intro N hND hNE hNv hN0 z p hp
    conv_lhs => rw [← awayFrom_mul_ι_compAt (𝓞 K) K v p, ← mul_assoc]
    have hcongp := cong_compAt_of_mem_principalLevel hNv hN0 hp
    rw [hyv _ (mem_localLevelOne_of_cong v hc1 (le_of_eq (idealBound_pow v (c₀ + 1)).symm) hcongp),
      hyaway _ (awayFrom_mem_U (v := v) (k := k) hND hNE hN0 hE₀0 hp) (compAt_awayFrom (𝓞 K) K v p)]
  have hNs0 : D * v.asIdeal ^ (c₀ + 1) * E₀ ≠ ⊥ := mul_ne_zero (mul_ne_zero hD0 (pow_ne_zero _ v.ne_bot)) hE₀0
  have hinvS := hinv (D * v.asIdeal ^ (c₀ + 1) * E₀) ⟨v.asIdeal ^ (c₀ + 1) * E₀, by ring⟩
    ⟨D * v.asIdeal ^ (c₀ + 1), by ring⟩
    ⟨D * E₀, by ring⟩ hNs0
  have hS'' : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ¬ w.asIdeal ∣ D * v.asIdeal ^ (c₀ + 1) * E₀ := by
    intro w hwS; rw [mul_right_comm]; exact hSgen (c₀ + 1) w hwS
  have hsys2 : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
      ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → GL (Fin 2) (w.adicCompletion K),
        HeckeIntegralSeam.IsHeckeCosetSystem
            (principalLevel (𝓞 K) K (D * E₀ * v.asIdeal ^ (M + 2 * n)) ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K w) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) ∧
          HeckeIntegralSeam.IsHeckeCosetSystem
            (principalLevel (𝓞 K) K (D * v.asIdeal ^ (c₀ + 1) * E₀) ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K w)
            (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K w (r i))) :=
    fun w hwS => hsys_principal_pair (hSgen (M + 2 * n) w hwS) (hS'' w hwS)
  have hyIsoS := relevel cK uK d₁K d₂K TK ξ S π (D * E₀ * v.asIdeal ^ (M + 2 * n)) (D * v.asIdeal ^ (c₀ + 1) * E₀) _
    hyIso
    (fun z p hp => by rw [← hyfun]; exact hinvS z p hp) hsys2

  refine ⟨c₀ + 1, _, hyIsoS, fun z p hp => ?_, hycutm, hy0'⟩
  rw [← hyfun]
  exact invariant_outputGroup (c₀ + 1) k (mul_ne_zero hD0 (pow_ne_zero _ v.ne_bot)) hE₀0 hyv hyaway z hp

end
end
end S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_levelOne_pow_invariant_isIsotypicCuspFormAt_principalLevel_ne_zero_of_ne_zero (solution)
