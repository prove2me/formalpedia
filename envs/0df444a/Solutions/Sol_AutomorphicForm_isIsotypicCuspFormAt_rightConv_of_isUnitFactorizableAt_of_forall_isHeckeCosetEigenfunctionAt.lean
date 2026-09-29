-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0f7e0bfb-4e80-5b5b-b9e2-304b52d5b19e

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_RingTheory_DedekindDomain_AdicValuation
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "AutomorphicForm~continuous_unipotentGL2 AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp"
open IsDedekindDomain MeasureTheory

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

private theorem ι_apply (h : GL (Fin 2) (v.adicCompletion K)) :
    ι R K v h = AdelicDock.finEmbed R K (AdelicDock.localEmbed R K v h) := rfl

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

namespace IsotypicConvolution
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

end IsotypicConvolution.LevelComponents

section
p2m_open "IsDedekindDomain NumberField AutomorphicForm~continuous_unipotentGL2 FLT.SmoothVectors"
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

end

section
p2m_open "IsDedekindDomain NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm~continuous_unipotentGL2 MeasureTheory"
open scoped Topology

namespace CuspidalConvolution

variable (K : Type) [Field K] [NumberField K]

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 K)) := by
  have huniv : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, exists_eq']
  have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
    rw [huniv]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hc
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

private theorem secondCountableTopology_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI := countable_heightOneSpectrum K
  exact RestrictedProduct.secondCountableTopology
    (X := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (C := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => NumberField.isOpenAdicCompletionIntegers K v)

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := fun v => by
    haveI := properSpace_completion K v
    infer_instance
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))

private theorem secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) := by
  haveI := secondCountableTopology_finiteAdeleRing K
  haveI := secondCountableTopology_infiniteAdeleRing K
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

private theorem continuous_unipotentGL2 :
    Continuous (unipotentGL2 : AdeleRing (𝓞 K) K → GL (Fin 2) (AdeleRing (𝓞 K) K)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

variable {K}

private theorem isCuspidalFn_rightConv (u f : AdelicGL2 (𝓞 K) K → ℂ) (hu : Continuous u)
    (hcu : @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 u)
    (hfc : Continuous f) (hfs : HasCompactSupport f) :
    @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2
      (rightConv K u f) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI := borelSpace_adeleBorel (𝓞 K) K
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := secondCountableTopology_adeleRing K
  intro g

  set μA : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμA
  set μG : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμG
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  set T : Set (AdelicGL2 (𝓞 K) K) := tsupport f with hT
  have hBm : MeasurableSet B := measurableSet_adelicBox K
  have hTc : IsCompact T := hfs
  have hTm : MeasurableSet T := (isClosed_tsupport f).measurableSet
  have hBfin : μA B ≠ ⊤ := (adelicAddHaar_adelicBox_lt_top K).ne
  have hTfin : μG T ≠ ⊤ := hTc.measure_lt_top.ne
  haveI : IsFiniteMeasure (μA.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  haveI : IsFiniteMeasure (μG.restrict T) := isFiniteMeasure_restrict.mpr hTfin

  have hrc : ∀ h : AdelicGL2 (𝓞 K) K, rightConv K u f h = ∫ y, u (h * y) * f y ∂(μG.restrict T) := by
    intro h
    rw [rightConv_apply]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

  set F : AdeleRing (𝓞 K) K → AdelicGL2 (𝓞 K) K → ℂ := fun x y => u (unipotentGL2 x * g * y) * f y with hF

  have hFcont : Continuous (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    exact (hu.comp ((((continuous_unipotentGL2 K).comp continuous_fst).mul continuous_const).mul
      continuous_snd)).mul (hfc.comp continuous_snd)
  obtain ⟨Cb, hCb, hBCb⟩ := exists_isCompact_adelicBox_subset K
  obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hfs
  have hKc : IsCompact ((fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K => unipotentGL2 p.1 * g * p.2) ''
      (Cb ×ˢ T)) :=
    (hCb.prod hTc).image ((((continuous_unipotentGL2 K).comp continuous_fst).mul continuous_const).mul
      continuous_snd)
  obtain ⟨Cu, hCu⟩ := hKc.exists_bound_of_continuousOn hu.continuousOn
  have hint : Integrable (Function.uncurry F) ((μA.restrict B).prod (μG.restrict T)) := by
    refine memLp_one_iff_integrable.mp (MemLp.of_bound hFcont.aestronglyMeasurable (Cu * Cf) ?_)
    have hae : ∀ᵐ p ∂((μA.restrict B).prod (μG.restrict T)), p ∈ B ×ˢ T := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (hBm.prod hTm)]
      filter_upwards [ae_restrict_mem hBm] with x hx
      filter_upwards [ae_restrict_mem hTm] with y hy
      exact ⟨hx, hy⟩
    refine hae.mono ?_
    rintro ⟨x, y⟩ ⟨hxB, hyT⟩
    have hx : unipotentGL2 x * g * y ∈ (fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        unipotentGL2 p.1 * g * p.2) '' (Cb ×ˢ T) :=
      ⟨(x, y), ⟨hBCb hxB, hyT⟩, rfl⟩
    have h1 : ‖u (unipotentGL2 x * g * y)‖ ≤ Cu := hCu _ hx
    have h0 : (0 : ℝ) ≤ Cu := (norm_nonneg _).trans h1
    simp only [Function.uncurry_apply_pair, hF, norm_mul]
    exact mul_le_mul h1 (hCf y) (norm_nonneg _) h0

  have hinner : ∀ y : AdelicGL2 (𝓞 K) K, ∫ x, F x y ∂(μA.restrict B) = 0 := by
    intro y
    have h := hcu (g * y)
    simp only [constantTerm, constantTermIntegrand, ProbabilityTheory.cond, integral_smul_measure] at h
    have hB0 : μA B ≠ 0 := (adelicAddHaar_adelicBox_pos K).ne'
    have hscalar : ((μA B)⁻¹).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr hBfin, ENNReal.inv_ne_top.mpr hB0⟩
    have h0 : ∫ x, u (unipotentGL2 x * (g * y)) ∂(μA.restrict B) = 0 := (smul_eq_zero.mp h).resolve_left hscalar
    simp only [hF, ← mul_assoc] at h0 ⊢
    rw [integral_mul_const, h0, zero_mul]

  show constantTerm _ unipotentGL2 (rightConv K u f) g = 0
  simp only [constantTerm, constantTermIntegrand, ProbabilityTheory.cond, integral_smul_measure]
  simp_rw [hrc]
  have hswap := integral_integral_swap hint
  simp only [hF] at hswap ⊢
  rw [hswap]
  simp only [hF] at hinner
  simp_rw [hinner]
  simp

end CuspidalConvolution

end

namespace IsotypicConvolution

section Ext

variable (𝕜 : Type*) [Field 𝕜] {H G : Type*} [Group H] [Group G] (ι : H →* G)

private def rightRep : Representation 𝕜 H (G → 𝕜) where
  toFun k :=
    { toFun := fun φ x => φ (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change φ (x * ι 1) = φ x
    rw [map_one, mul_one]
  map_mul' k₁ k₂ := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change φ (x * ι (k₁ * k₂)) = φ (x * ι k₁ * ι k₂)
    rw [map_mul, mul_assoc]

@[scoped simp] private theorem rightRep_apply (k : H) (φ : G → 𝕜) (x : G) : rightRep 𝕜 ι k φ x = φ (x * ι k) := rfl

private theorem rightRep_congr {a b : H} (h : ι a = ι b) (φ : G → 𝕜) : rightRep 𝕜 ι a φ = rightRep 𝕜 ι b φ := by
  funext x
  rw [rightRep_apply, rightRep_apply, h]

private theorem rightRep_mul_apply (a b : H) (φ : G → 𝕜) :
    rightRep 𝕜 ι a (rightRep 𝕜 ι b φ) = rightRep 𝕜 ι (a * b) φ := by
  rw [map_mul]
  rfl

private noncomputable def _root_.IsotypicConvolution.trans (x : G) : G := Quotient.out (x : G ⧸ ι.range)

p2m_export "IsotypicConvolution" "trans"
private theorem mk_trans (x : G) : ((trans ι x : G) : G ⧸ ι.range) = (x : G ⧸ ι.range) :=
  QuotientGroup.out_eq' _

private theorem trans_inv_mul_mem (x : G) : (trans ι x)⁻¹ * x ∈ ι.range :=
  QuotientGroup.eq.mp (mk_trans ι x)

private theorem exists_sect (x : G) : ∃ h : H, ι h = (trans ι x)⁻¹ * x :=
  MonoidHom.mem_range.mp (trans_inv_mul_mem ι x)

private noncomputable def sect (x : G) : H := (exists_sect ι x).choose

private theorem ι_sect (x : G) : ι (sect ι x) = (trans ι x)⁻¹ * x := (exists_sect ι x).choose_spec

private theorem trans_mul_ι_sect (x : G) : trans ι x * ι (sect ι x) = x := by
  rw [ι_sect, mul_inv_cancel_left]

private theorem mk_mul_ι (x : G) (k : H) : ((x * ι k : G) : G ⧸ ι.range) = (x : G ⧸ ι.range) := by
  refine QuotientGroup.eq.mpr ?_
  rw [mul_inv_rev, inv_mul_cancel_right]
  exact ⟨k⁻¹, map_inv ι k⟩

private theorem trans_mul_ι (x : G) (k : H) : trans ι (x * ι k) = trans ι x := by
  unfold trans
  rw [mk_mul_ι]

private theorem ι_sect_mul_ι (x : G) (k : H) : ι (sect ι (x * ι k)) = ι (sect ι x * k) := by
  rw [ι_sect, trans_mul_ι, map_mul, ι_sect, mul_assoc]

private theorem exists_equivariant_extension (Y : Submodule 𝕜 (G → 𝕜))
    (hY : ∀ (k : H) (φ : G → 𝕜), φ ∈ Y → rightRep 𝕜 ι k φ ∈ Y)
    (Φ : Y →ₗ[𝕜] (G → 𝕜))
    (hΦ : ∀ (k : H) (y : Y), Φ ⟨rightRep 𝕜 ι k y, hY k y y.2⟩ = rightRep 𝕜 ι k (Φ y)) :
    ∃ Ψ : (G → 𝕜) →ₗ[𝕜] (G → 𝕜),
      (∀ (k : H) (φ : G → 𝕜), Ψ (rightRep 𝕜 ι k φ) = rightRep 𝕜 ι k (Ψ φ)) ∧
      ∀ y : Y, Ψ y = Φ y := by
  classical
  obtain ⟨πY, hπ⟩ := Y.subtype.exists_leftInverse_of_injective Y.ker_subtype

  let Λ : (G → 𝕜) →ₗ[𝕜] (G ⧸ ι.range → 𝕜) :=
    { toFun := fun φ q => Φ (πY φ) (Quotient.out q)
      map_add' := fun φ₁ φ₂ => funext fun q => by
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c φ => funext fun q => by
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  let Ψ : (G → 𝕜) →ₗ[𝕜] (G → 𝕜) :=
    { toFun := fun φ x => Λ (rightRep 𝕜 ι (sect ι x) φ) (x : G ⧸ ι.range)
      map_add' := fun φ₁ φ₂ => funext fun x => by
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c φ => funext fun x => by
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨Ψ, fun k φ => funext fun x => ?_, fun y => funext fun x => ?_⟩
  ·
    change Λ (rightRep 𝕜 ι (sect ι x) (rightRep 𝕜 ι k φ)) (x : G ⧸ ι.range)
        = Λ (rightRep 𝕜 ι (sect ι (x * ι k)) φ) ((x * ι k : G) : G ⧸ ι.range)
    rw [rightRep_mul_apply, mk_mul_ι, rightRep_congr 𝕜 ι (ι_sect_mul_ι ι x k)]
  ·
    have hmem : rightRep 𝕜 ι (sect ι x) (y : G → 𝕜) ∈ Y := hY (sect ι x) y y.2
    have hπy : πY (rightRep 𝕜 ι (sect ι x) (y : G → 𝕜)) = ⟨_, hmem⟩ := by
      have h := LinearMap.congr_fun hπ ⟨_, hmem⟩
      simpa using h
    change Φ (πY (rightRep 𝕜 ι (sect ι x) (y : G → 𝕜))) (Quotient.out (x : G ⧸ ι.range)) = Φ y x
    rw [hπy, hΦ (sect ι x) y, rightRep_apply]
    change Φ y (trans ι x * ι (sect ι x)) = Φ y x
    rw [trans_mul_ι_sect]

end Ext

section Generic

variable {H G : Type*} [Group H] [Group G]

private theorem linearMap_mem_typeSubmodule {W : Type*} [AddCommGroup W] [Module ℂ W] (ι : H →* G)
    (ρ : Representation ℂ H W) (Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hΨ : ∀ (k : H) (φ : G → ℂ), Ψ (rightRep ℂ ι k φ) = rightRep ℂ ι k (Ψ φ)) :
    ∀ φ ∈ typeSubmodule ι ρ, Ψ φ ∈ typeSubmodule ι ρ := by
  intro φ hφ
  refine Submodule.span_induction (p := fun φ _ => Ψ φ ∈ typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι ρ (Ψ ∘ₗ T) := by
      intro k v' x
      show Ψ (T (ρ k v')) x = Ψ (T v') (x * ι k)
      have hTv : T (ρ k v') = rightRep ℂ ι k (T v') := funext fun y => hT k v' y
      rw [hTv, hΨ]
      rfl
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · show Ψ 0 ∈ typeSubmodule ι ρ
    rw [map_zero]
    exact (typeSubmodule ι ρ).zero_mem
  · intro _ _ _ _ hu hw
    rw [map_add]
    exact (typeSubmodule ι ρ).add_mem hu hw
  · intro c _ _ hu
    rw [map_smul]
    exact (typeSubmodule ι ρ).smul_mem c hu

private theorem linearMap_mem_iSup {M : Type*} [AddCommGroup M] [Module ℂ M] {n : Type*} (S : n → Submodule ℂ M)
    (L : M →ₗ[ℂ] M) (hS : ∀ i, ∀ φ ∈ S i, L φ ∈ S i) : ∀ φ ∈ ⨆ i, S i, L φ ∈ ⨆ i, S i := by
  intro φ hφ
  have hle : Submodule.map L (⨆ i, S i) ≤ ⨆ i, S i := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => Submodule.map_le_iff_le_comap.mpr fun ψ hψ => hS i ψ hψ
  exact hle (Submodule.mem_map_of_mem hφ)

end Generic

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

private theorem rightConv_apply_mul_of_conj_invariant (u f : AdelicGL2 (𝓞 K) K → ℂ) (t : AdelicGL2 (𝓞 K) K)
    (hft : ∀ y, f (t * y * t⁻¹) = f y) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K u f (g * t) = rightConv K (fun x => u (x * t)) f g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  simp only [rightConv_apply]
  have h1 : ∫ x, u (g * x * t) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ x, u (g * (t * x) * t) * f (t * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (integral_mul_left_eq_self (fun y => u (g * y * t) * f y) t).symm
  have h2 : ∫ x, u (g * (t * x) * t) * f (t * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ x, u (g * (t * (x * t⁻¹)) * t) * f (t * (x * t⁻¹)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (integral_mul_right_eq_self (fun x => u (g * (t * x) * t) * f (t * x)) t⁻¹).symm
  rw [h1, h2]
  congr 1
  funext x
  rw [show g * (t * (x * t⁻¹)) * t = g * t * x by simp only [mul_assoc, inv_mul_cancel, mul_one],
    show t * (x * t⁻¹) = t * x * t⁻¹ from (mul_assoc _ _ _).symm, hft]

private theorem rightConv_comp_mul_of_conj_invariant (u f : AdelicGL2 (𝓞 K) K → ℂ) (t : AdelicGL2 (𝓞 K) K)
    (hft : ∀ y, f (t * y * t⁻¹) = f y) :
    (fun x => rightConv K u f (x * t)) = rightConv K (fun x => u (x * t)) f :=
  funext fun g => rightConv_apply_mul_of_conj_invariant u f t hft g

private def contSubmodule : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := continuous_const
  smul_mem' := fun c _ hφ => hφ.const_smul c

private theorem mem_contSubmodule {φ : AdelicGL2 (𝓞 K) K → ℂ} : φ ∈ (contSubmodule : Submodule ℂ _) ↔ Continuous φ :=
  Iff.rfl

private theorem rightConv_mem_archCutSubmodule (u f : AdelicGL2 (𝓞 K) K → ℂ) (hu : Continuous u)
    (hf : IsFactorizableTestFn K f)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y)
    (tys : ArchTypeFamily K) (hut : u ∈ archCutSubmodule K tys) :
    rightConv K u f ∈ archCutSubmodule K tys := by
  have hfc : Continuous f := continuous_of_isFactorizableTestFn hf
  have hfs : HasCompactSupport f := hasCompactSupport_of_isFactorizableTestFn hf
  rw [mem_archCutSubmodule_iff] at hut ⊢
  intro w

  let S : Fin (tys.card w) → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := fun i => archTypeSubmoduleAt K w (tys.rep w i)
  have hS : ∀ (i) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ S i,
      rightRep ℂ (rowIsometryInclAt₀ K w) k φ ∈ S i :=
    fun i k φ hφ => comp_mul_mem_typeSubmodule hφ k
  let Y : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := (⨆ i, S i) ⊓ contSubmodule
  have hY : ∀ (k : rowIsometrySubgroup₀ w.Completion) (φ : AdelicGL2 (𝓞 K) K → ℂ), φ ∈ Y →
      rightRep ℂ (rowIsometryInclAt₀ K w) k φ ∈ Y := by
    intro k φ hφ
    obtain ⟨hφS, hφc⟩ := Submodule.mem_inf.mp hφ
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact linearMap_mem_iSup S (rightRep ℂ (rowIsometryInclAt₀ K w) k) (fun i ψ hψ => hS i k ψ hψ) φ hφS
    · exact (mem_contSubmodule.mp hφc).comp (continuous_id.mul continuous_const)

  let Φ : Y →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun y => rightConv K (y : AdelicGL2 (𝓞 K) K → ℂ) f
      map_add' := fun y₁ y₂ => by
        rw [Submodule.coe_add]
        exact rightConv_add_left K (mem_contSubmodule.mp (Submodule.mem_inf.mp y₁.2).2)
          (mem_contSubmodule.mp (Submodule.mem_inf.mp y₂.2).2) hfc hfs
      map_smul' := fun c y => by
        rw [Submodule.coe_smul, RingHom.id_apply]
        exact convOp_smul K f c _ }
  have hΦ : ∀ (k : rowIsometrySubgroup₀ w.Completion) (y : Y),
      Φ ⟨rightRep ℂ (rowIsometryInclAt₀ K w) k y, hY k y y.2⟩ = rightRep ℂ (rowIsometryInclAt₀ K w) k (Φ y) := by
    intro k y
    show rightConv K (fun x => (y : AdelicGL2 (𝓞 K) K → ℂ) (x * rowIsometryInclAt₀ K w k)) f
        = fun x => rightConv K (y : AdelicGL2 (𝓞 K) K → ℂ) f (x * rowIsometryInclAt₀ K w k)
    exact (rightConv_comp_mul_of_conj_invariant _ f _ (hfK w k)).symm
  obtain ⟨Ψ, hΨeq, hΨext⟩ := exists_equivariant_extension ℂ (rowIsometryInclAt₀ K w) Y hY Φ hΦ

  have hmap : ∀ φ ∈ ⨆ i, S i, Ψ φ ∈ ⨆ i, S i :=
    linearMap_mem_iSup S Ψ fun i φ hφ =>
      linearMap_mem_typeSubmodule (rowIsometryInclAt₀ K w) (tys.rep w i).ρ Ψ hΨeq φ hφ
  have huY : u ∈ Y := Submodule.mem_inf.mpr ⟨hut w, mem_contSubmodule.mpr hu⟩
  have hΨu : rightConv K u f = Ψ u := (hΨext ⟨u, huY⟩).symm
  rw [hΨu]
  exact hmap u (hut w)

end Basics

end IsotypicConvolution
p2m_reactivate "P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt.IsotypicConvolution"

namespace IsotypicConvolution

section HeckeRelocation

open PlaceEmbedding

variable {K : Type} [Field K] [NumberField K]

private theorem compAt_mem_localIntegralSet {S : Finset (HeightOneSpectrum (𝓞 K))} {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsUnitFactorizableAt K ⊥ S f) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    {x : AdelicGL2 (𝓞 K) K} (hx : f x ≠ 0) : compAt (𝓞 K) K v x ∈ localIntegralSet K v := by
  obtain ⟨-, fa, ff, fS, -, -, -, -, hvan, hfg⟩ := hf
  by_contra h
  exact hx (by rw [hfg x, hvan _ ⟨v, hv, h⟩, mul_zero])

private theorem ι_compAt_mem_principal {N : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)} (hvN : ¬ v.asIdeal ∣ N)
    {x : AdelicGL2 (𝓞 K) K} (hx : compAt (𝓞 K) K v x ∈ localIntegralSet K v) :
    ι (𝓞 K) K v (compAt (𝓞 K) K v x) ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  obtain ⟨hint, hinv⟩ := (mem_localIntegralSet K v).mp hx
  exact LevelComponents.supported_mem_P K v hvN (LevelComponents.mem_localLevelOne_of_integral K v hvN hint hinv)

private theorem isHeckeCosetEigenfunctionAt_rightConv
    (UB : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (N N'' : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : Continuous u)
    (hulev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      u (g * x) = u g)
    (huhecke : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      IsHeckeCosetEigenfunctionAt K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v u (π.a v))
    (hsys : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ r : Fin (Ideal.absNorm v.asIdeal + 1) → GL (Fin 2) (v.adicCompletion K),
        HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K v) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (r i))) ∧
          HeckeIntegralSeam.IsHeckeCosetSystem (UB N'') (heckeGen (𝓞 K) K v)
            (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (r i))))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsUnitFactorizableAt K ⊥ S f)
    (hfL : ∀ x ∈ UB N'', ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    IsHeckeCosetEigenfunctionAt K (UB N'') (heckeGen (𝓞 K) K v) v (rightConv K u f) (π.a v) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have _hfL := hfL
  have hvN : ¬ v.asIdeal ∣ N := fun h => hv (hN v h)
  obtain ⟨r, hsysP, hsysU⟩ := hsys v hv
  obtain ⟨reps₀, hsys₀, hsum₀⟩ := huhecke v hv
  have hsysP' : HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) (fun i => ι (𝓞 K) K v (r i)) := hsysP
  have hsysU' : HeckeIntegralSeam.IsHeckeCosetSystem (UB N'') (heckeGen (𝓞 K) K v)
      (fun i => ι (𝓞 K) K v (r i)) := hsysU
  have hff : IsFactorizableTestFn K f := hf.isFactorizableTestFn
  have hfc : Continuous f := continuous_of_isFactorizableTestFn hff
  have hfs : HasCompactSupport f := hasCompactSupport_of_isFactorizableTestFn hff
  refine ⟨fun i => ι (𝓞 K) K v (r i), hsysU', fun g => ?_⟩

  have hpt : ∀ x : AdelicGL2 (𝓞 K) K,
      (∑ i, u (g * ι (𝓞 K) K v (r i) * x)) * f x = π.a v * u (g * x) * f x := by
    intro x
    by_cases hx : f x = 0
    · rw [hx, mul_zero, mul_zero]
    · have hxv : compAt (𝓞 K) K v x ∈ localIntegralSet K v := compAt_mem_localIntegralSet hf hv hx
      have hkP : ι (𝓞 K) K v (compAt (𝓞 K) K v x) ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
        ι_compAt_mem_principal hvN hxv
      have hsplit : awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (compAt (𝓞 K) K v x) = x :=
        awayFrom_mul_ι_compAt (𝓞 K) K v x
      have hterm : ∀ i, u (g * ι (𝓞 K) K v (r i) * x) = u (g * awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (r i)) := by
        intro i
        have hmid : g * ι (𝓞 K) K v (r i) * awayFrom (𝓞 K) K v x
            = g * awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (r i) := by
          rw [mul_assoc, ι_mul_awayFrom_comm, ← mul_assoc]
        calc u (g * ι (𝓞 K) K v (r i) * x)
            = u (g * ι (𝓞 K) K v (r i) * (awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (compAt (𝓞 K) K v x))) := by
                rw [hsplit]
          _ = u (g * awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (r i) * ι (𝓞 K) K v (compAt (𝓞 K) K v x)) := by
                rw [← mul_assoc, hmid]
          _ = u (g * awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (r i)) := hulev _ _ hkP
      have hco : (∑ i, u (g * awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (r i)))
          = ∑ i, u (g * awayFrom (𝓞 K) K v x * reps₀ i) :=
        HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys₀ hsysP' hulev _
      have h0 : (∑ i, u (g * awayFrom (𝓞 K) K v x * reps₀ i)) = π.a v * u (g * awayFrom (𝓞 K) K v x) :=
        hsum₀ _
      have hback : u (g * awayFrom (𝓞 K) K v x) = u (g * x) := by
        rw [← hulev (g * awayFrom (𝓞 K) K v x) _ hkP, mul_assoc, hsplit]
      calc (∑ i, u (g * ι (𝓞 K) K v (r i) * x)) * f x
          = (∑ i, u (g * awayFrom (𝓞 K) K v x * ι (𝓞 K) K v (r i))) * f x := by
              rw [Finset.sum_congr rfl fun i _ => hterm i]
        _ = π.a v * u (g * x) * f x := by rw [hco, h0, hback]

  have hint : ∀ i, Integrable (fun x => u (g * ι (𝓞 K) K v (r i) * x) * f x) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    fun i => ((hu.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  show (∑ i, rightConv K u f (g * ι (𝓞 K) K v (r i))) = π.a v * rightConv K u f g
  simp only [rightConv_apply]
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (∑ i, u (g * ι (𝓞 K) K v (r i) * x) * f x) = π.a v * (u (g * x) * f x)
  rw [← Finset.sum_mul, ← mul_assoc]
  exact hpt x

end HeckeRelocation
p2m_reactivate "P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt.IsotypicConvolution"

section Conclusion

variable {K : Type} [Field K] [NumberField K]

private theorem rightConv_mul_left_of_invariant (φ f : AdelicGL2 (𝓞 K) K → ℂ)
    (h : AdelicGL2 (𝓞 K) K) (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (h * g) = rightConv K φ f g := by
  rw [← rightConv_comp_mul_left]
  exact congrArg (fun ψ => rightConv K ψ f g) (funext hφ)

private theorem rightConv_mul_left_of_eq_smul (φ f : AdelicGL2 (𝓞 K) K → ℂ)
    (h : AdelicGL2 (𝓞 K) K) (a : ℂ) (hφ : ∀ x, φ (h * x) = a * φ x) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (h * g) = a * rightConv K φ f g := by
  rw [← rightConv_comp_mul_left, (funext hφ : (fun x => φ (h * x)) = fun x => a * φ x)]
  simp only [rightConv, mul_assoc]
  exact integral_const_mul a _

private theorem rightConv_apply_mul_of_left_invariant (φ f : AdelicGL2 (𝓞 K) K → ℂ)
    (g t : AdelicGL2 (𝓞 K) K) (hf : ∀ y, f (t⁻¹ * y) = f y) :
    rightConv K φ f (g * t) = rightConv K φ f g := by
  rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  exact congrArg (fun f' => rightConv K φ f' g) (funext hf)

private theorem memLp_two_restrict_of_norm_le {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {D : Set α} (hD : μ D < ⊤) {φ : α → ℂ} (hmeas : AEStronglyMeasurable φ (μ.restrict D))
    (hDm : MeasurableSet D) {C : ℝ} (hC : ∀ g ∈ D, ‖φ g‖ ≤ C) :
    MemLp φ 2 (μ.restrict D) := by
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.mpr hD.ne
  exact MemLp.of_bound hmeas C ((ae_restrict_iff' hDm).mpr (Filter.Eventually.of_forall hC))

private theorem _root_.IsotypicConvolution.isCuspidalFn_rightConv (u f : AdelicGL2 (𝓞 K) K → ℂ) (hu : Continuous u)
    (hcu : @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 u)
    (hf : IsFactorizableTestFn K f) :
    @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2
      (rightConv K u f) :=
  CuspidalConvolution.isCuspidalFn_rightConv u f hu hcu (continuous_of_isFactorizableTestFn hf)
    (hasCompactSupport_of_isFactorizableTestFn hf)

p2m_export "IsotypicConvolution" "isCuspidalFn_rightConv"

private theorem _root_.IsotypicConvolution.isKfSmooth_rightConv (u f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    IsKfSmooth K (rightConv K u f) :=
  SmoothConvolution.isKfSmooth_rightConv u f hf

p2m_export "IsotypicConvolution" "isKfSmooth_rightConv"
end Conclusion
p2m_reactivate "P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt.IsotypicConvolution"

end IsotypicConvolution
p2m_reactivate "P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt.IsotypicConvolution"

open IsotypicConvolution in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (UB : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N N'' : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S π u)
    (hsys : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ r : Fin (Ideal.absNorm v.asIdeal + 1) → GL (Fin 2) (v.adicCompletion K),
        HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K v) (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (r i))) ∧
          HeckeIntegralSeam.IsHeckeCosetSystem (UB N'') (heckeGen (𝓞 K) K v)
            (fun i => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (r i))))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsUnitFactorizableAt K ⊥ S f)
    (hfL : ∀ x ∈ UB N'', ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g)
    (hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) :
    IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          UB (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        ξ N'' S π (rightConv K u f) ∧
      ∀ tys : ArchTypeFamily K, u ∈ archCutSubmodule K tys → rightConv K u f ∈ archCutSubmodule K tys := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  have hff : IsFactorizableTestFn K f := hf.isFactorizableTestFn
  have hucont : Continuous u := hu.continuous
  obtain ⟨hcont', -⟩ :=
    AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K u hucont f hff

  have hLs : IsLsXiFunction (𝓞 K) K _ ξ u :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ u).mp hu.smoothCusp.1.1).1
  have hLs' : IsLsXiFunction (𝓞 K) K _ ξ (rightConv K u f) :=
    ⟨fun γ g => rightConv_mul_left_of_invariant u f _ (hLs.left_invariant γ) g,
     fun z g => rightConv_mul_left_of_eq_smul u f _ _ (hLs.central_transform z) g⟩

  have hDm : MeasurableSet (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K) := by
    refine TK.measurableSet_biUnion fun x _ => ?_
    have h := (MeasurableEquiv.mulRight x).measurableSet_image.mpr
      (measurableSet_centreCutSiegelSet (F := K) cK uK d₁K d₂K)
    simpa only [MeasurableEquiv.coe_mulRight] using h
  have hDfin : adelicGLHaar (Fin 2) (𝓞 K) K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K) < ⊤ := by
    refine lt_of_le_of_lt (measure_biUnion_finset_le TK _) ?_
    exact ENNReal.sum_lt_top.mpr fun x _ =>
      adelicGLHaar_mul_right_centreCutSiegelSet_lt_top K hcK uK hd₁K d₂K x
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
      K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK ξ f hff
  have hMem : MemLp (rightConv K u f) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)) :=
    memLp_two_restrict_of_norm_le hDfin hcont'.aestronglyMeasurable hDm (hC u hu.smoothCusp hu.continuous)

  have hcusp := isCuspidalFn_rightConv u f hucont hu.smoothCusp.1.2 hff
  have hsm := isKfSmooth_rightConv u f hff
  refine ⟨{ smoothCusp := ⟨⟨(lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ _).mpr ⟨hLs', hMem⟩, hcusp⟩, hsm⟩
            continuous := hcont'
            level_invariant := fun g x hx =>
              rightConv_apply_mul_of_left_invariant u f g x fun y => hfL x⁻¹ ((UB N'').inv_mem hx) y
            hecke_eigen := fun v hv =>
              isHeckeCosetEigenfunctionAt_rightConv UB N N'' S hN π u hucont hu.level_invariant hu.hecke_eigen
                hsys f hf hfL v hv
            central_eigen := fun v hv g =>
              rightConv_mul_left_of_eq_smul u f _ _ (hu.central_eigen v hv) g }, ?_⟩
  exact fun tys hut => rightConv_mem_archCutSubmodule u f hucont hff hfK tys hut

end
end S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt (solution)
