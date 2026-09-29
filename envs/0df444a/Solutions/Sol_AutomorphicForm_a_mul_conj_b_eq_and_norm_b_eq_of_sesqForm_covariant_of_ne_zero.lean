-- Prove2me | solution 1 for AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c5134227-4419-58b0-ae1e-369432443249

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

namespace TableUnitarity

variable {G : Type*} [Group G]

private def rt (φ : G → ℂ) (t : G) : G → ℂ := fun z => φ (z * t)

@[scoped simp] private theorem rt_apply (φ : G → ℂ) (t z : G) : rt φ t z = φ (z * t) := rfl

private theorem rt_one (φ : G → ℂ) : rt φ 1 = φ := by
  funext z
  simp [rt]

private theorem rt_mul (φ : G → ℂ) (g t : G) : rt φ (g * t) = rt (rt φ t) g := by
  funext z
  simp [rt, mul_assoc]

section Core

variable {U : Subgroup G} {φ : G → ℂ} (hU : ∀ x : G, ∀ u ∈ U, φ (x * u) = φ x)
variable {V : Submodule ℂ (G → ℂ)} (hV : ∀ t : G, rt φ t ∈ V)
variable (P : (G → ℂ) →ₗ[ℂ] (G → ℂ) →ₗ⋆[ℂ] ℂ) {c : G → ℂ}
variable (hP : ∀ (g : G) (x y : G → ℂ), x ∈ V → y ∈ V →
  P (fun z => x (z * g)) (fun z => y (z * g)) = c g * P x y)
variable (hself : P φ φ ≠ 0)

include hU in
private theorem rt_mem_eq (u : G) (hu : u ∈ U) : rt φ u = φ := by
  funext z
  exact hU z u hu

include hV in
private theorem self_mem : φ ∈ V := by
  have h := hV 1
  rwa [rt_one] at h

include hV hP in

private theorem P_rt_rt (g t t' : G) :
    P (rt φ (g * t)) (rt φ (g * t')) = c g * P (rt φ t) (rt φ t') := by
  rw [rt_mul φ g t, rt_mul φ g t']
  exact hP g (rt φ t) (rt φ t') (hV t) (hV t')

include hU hV hP hself in

private theorem c_eq_one (u : G) (hu : u ∈ U) : c u = 1 := by
  have h := hP u φ φ (self_mem hV) (self_mem hV)
  have e : (fun z => φ (z * u)) = φ := rt_mem_eq hU u hu
  rw [e] at h
  exact mul_right_cancel₀ hself (h.symm.trans (one_mul _).symm)

include hU in

private theorem f_mul_mem_right (t u : G) (hu : u ∈ U) : P φ (rt φ (t * u)) = P φ (rt φ t) := by
  rw [rt_mul, rt_mem_eq hU u hu]

include hU hV hP hself in

private theorem f_mul_mem_left (t u : G) (hu : u ∈ U) : P φ (rt φ (u * t)) = P φ (rt φ t) := by
  have h := P_rt_rt hV P hP u 1 t
  rw [mul_one, rt_one, c_eq_one hU hV P hP hself u hu, one_mul, rt_mem_eq hU u hu] at h
  exact h

include hU in

private theorem g_mul_mem_right (t u : G) (hu : u ∈ U) : P (rt φ (t * u)) φ = P (rt φ t) φ := by
  rw [rt_mul, rt_mem_eq hU u hu]

include hU hV hP hself in

private theorem g_mul_mem_left (t u : G) (hu : u ∈ U) : P (rt φ (u * t)) φ = P (rt φ t) φ := by
  have h := P_rt_rt hV P hP u t 1
  rw [mul_one, rt_one, c_eq_one hU hV P hP hself u hu, one_mul, rt_mem_eq hU u hu] at h
  exact h

include hU hV hP hself in

private theorem f_doubleCoset (g : G) {t : G} (ht : ∃ u ∈ U, ∃ u' ∈ U, u * g * u' = t) :
    P φ (rt φ t) = P φ (rt φ g) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := ht
  rw [f_mul_mem_right hU P (u * g) u' hu', f_mul_mem_left hU hV P hP hself g u hu]

include hU hV hP hself in

private theorem g_doubleCoset (g : G) {t : G} (ht : ∃ u ∈ U, ∃ u' ∈ U, u * g * u' = t) :
    P (rt φ t) φ = P (rt φ g) φ := by
  obtain ⟨u, hu, u', hu', rfl⟩ := ht
  rw [g_mul_mem_right hU P (u * g) u' hu', g_mul_mem_left hU hV P hP hself g u hu]

include hV hP in

private theorem g_eq_c_mul_f (g : G) : P (rt φ g) φ = c g * P φ (rt φ g⁻¹) := by
  have h := P_rt_rt hV P hP g 1 g⁻¹
  rw [mul_one, mul_inv_cancel, rt_one] at h
  exact h

private theorem f_central_mul {zc : G} (hzc : ∀ x : G, zc * x = x * zc) {b : ℂ}
    (hb : ∀ x : G, φ (zc * x) = b * φ x) (t : G) :
    P φ (rt φ (zc * t)) = (starRingEnd ℂ) b * P φ (rt φ t) := by
  have e : rt φ (zc * t) = b • rt φ t := by
    funext z
    rw [rt_apply, Pi.smul_apply, rt_apply, smul_eq_mul, ← hb (z * t), ← mul_assoc, ← hzc z,
      mul_assoc]
  rw [e, map_smulₛₗ (P φ) b (rt φ t), smul_eq_mul]

private theorem rt_central {zc : G} (hzc : ∀ x : G, zc * x = x * zc) {b : ℂ}
    (hb : ∀ x : G, φ (zc * x) = b * φ x) : rt φ zc = b • φ := by
  funext z
  rw [rt_apply, Pi.smul_apply, smul_eq_mul, ← hzc z, hb z]

include hU hV hP hself in

private theorem eigen_mul_conj_central {ι : Type*} [Fintype ι] {gv : G} {reps : ι → G}
    (hmem : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, u * gv * u' = reps i) {a : ℂ}
    (ha : ∀ x : G, ∑ i, φ (x * reps i) = a * φ x)
    {zc : G} (hzc : ∀ x : G, zc * x = x * zc) {b : ℂ} (hb : ∀ x : G, φ (zc * x) = b * φ x)
    {w : G} (hw : w ∈ U) (hweyl : zc = w * gv * w⁻¹ * gv) :
    a * (starRingEnd ℂ) b = c gv * (starRingEnd ℂ) a := by

  have hsum : a • φ = ∑ i, rt φ (reps i) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, rt_apply, ha]

  have hE1 : (starRingEnd ℂ) a * P φ φ = ∑ _i : ι, P φ (rt φ gv) := by
    have h : P φ (a • φ) = (starRingEnd ℂ) a * P φ φ := by
      rw [map_smulₛₗ (P φ) a φ, smul_eq_mul]
    rw [← h, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => f_doubleCoset hU hV P hP hself gv (hmem i)

  have hE2 : a * P φ φ = ∑ _i : ι, c gv * P φ (rt φ gv⁻¹) := by
    have h : P (a • φ) φ = a * P φ φ := by
      rw [map_smul P a φ, LinearMap.smul_apply, smul_eq_mul]
    rw [← h, hsum, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ =>
      (g_doubleCoset hU hV P hP hself gv (hmem i)).trans (g_eq_c_mul_f hV P hP gv)

  have hE3 : P φ (rt φ gv) = (starRingEnd ℂ) b * P φ (rt φ gv⁻¹) := by
    have hzg : zc * gv⁻¹ = w * gv * w⁻¹ := by rw [hweyl, mul_inv_cancel_right]
    have h1 : P φ (rt φ (zc * gv⁻¹)) = P φ (rt φ gv) := by
      rw [hzg]
      exact f_doubleCoset hU hV P hP hself gv ⟨w, hw, w⁻¹, inv_mem hw, rfl⟩
    rw [← h1, f_central_mul P hzc hb]

  apply mul_right_cancel₀ hself
  calc a * (starRingEnd ℂ) b * P φ φ
      = (starRingEnd ℂ) b * (a * P φ φ) := by ring
    _ = (starRingEnd ℂ) b * ∑ _i : ι, c gv * P φ (rt φ gv⁻¹) := by rw [hE2]
    _ = ∑ _i : ι, c gv * ((starRingEnd ℂ) b * P φ (rt φ gv⁻¹)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ _i : ι, c gv * P φ (rt φ gv) := Finset.sum_congr rfl fun _ _ => by rw [hE3]
    _ = c gv * ∑ _i : ι, P φ (rt φ gv) := by rw [Finset.mul_sum]
    _ = c gv * ((starRingEnd ℂ) a * P φ φ) := by rw [hE1]
    _ = c gv * (starRingEnd ℂ) a * P φ φ := by ring

include hU hV hP hself in

private theorem central_mul_conj_central {gv zc : G} (hzc : ∀ x : G, zc * x = x * zc) {b : ℂ}
    (hb : ∀ x : G, φ (zc * x) = b * φ x) {w : G} (hw : w ∈ U)
    (hweyl : zc = w * gv * w⁻¹ * gv) :
    b * (starRingEnd ℂ) b = c gv * c gv := by

  have hL : P (rt φ zc) (rt φ zc) = b * (starRingEnd ℂ) b * P φ φ := by
    rw [rt_central hzc hb, map_smul P b φ, LinearMap.smul_apply, map_smulₛₗ (P φ) b φ,
      smul_eq_mul, smul_eq_mul, mul_assoc]

  have hR : P (rt φ zc) (rt φ zc) = c gv * c gv * P φ φ := by
    have e1 : zc = w * (gv * (w⁻¹ * gv)) := by
      rw [hweyl]
      group
    have e2 : c w = 1 := c_eq_one hU hV P hP hself w hw
    have e3 : c w⁻¹ = 1 := c_eq_one hU hV P hP hself w⁻¹ (inv_mem hw)
    have e4 : P (rt φ gv) (rt φ gv) = c gv * P φ φ := by
      have h := P_rt_rt hV P hP gv 1 1
      rwa [mul_one, rt_one] at h
    rw [e1, P_rt_rt hV P hP, e2, one_mul, P_rt_rt hV P hP, P_rt_rt hV P hP, e3, one_mul, e4,
      mul_assoc]
  exact mul_right_cancel₀ hself (hL.symm.trans hR)

end Core

end TableUnitarity
p2m_reactivate "P2MW.S_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero.TableUnitarity"

section WeylSection

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel LocalGL2 AdelicDock

namespace WeylDatum

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) :
    IsLocalLevelOne (𝓞 F) F v N m := by
  have hN : N ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have hb : AdelicLevel.idealBound (𝓞 F) N v = 1 :=
    AdelicLevel.idealBound_eq_one_of_not_dvd hN hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private theorem entries_mem_of_mem_integralSubgroup {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) (i j : Fin 2) :
    (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
  obtain ⟨y, rfl⟩ := hk
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact SetLike.coe_mem _

private theorem mem_localLevelOne_of_mem_integralSubgroup {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv (entries_mem_of_mem_integralSubgroup F v hk),
    isLocalLevelOne_of_integral F v hv
      (entries_mem_of_mem_integralSubgroup F v (inv_mem hk))⟩

private theorem finEmbed_localEmbed_mem_of_mem_integralSubgroup {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff]
    exact mem_localLevelOne_of_mem_integralSubgroup F v hv hk
  · exact (mem_finiteAdelicGL2Subgroup_iff F _).mpr (glArch_finEmbed (𝓞 F) F _)

private theorem weylInt_mul_self :
    weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) *
      weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_weylInt, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem weylInt_inv :
    (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))⁻¹ =
      weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) :=
  inv_eq_of_mul_eq_one_right (weylInt_mul_self F v)

private theorem coe_weylInt_mul_diagPi_mul_inv_mul_diagPi (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0) :
    ((weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) * diagPi ϖ hϖ0 *
        (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))⁻¹ * diagPi ϖ hϖ0 :
          GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.scalar (Fin 2) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) := by
  rw [weylInt_inv, Units.val_mul, Units.val_mul, Units.val_mul, coe_weylInt, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]

private theorem det_coe_diagPi (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0) :
    Matrix.det ((diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ := by
  rw [coe_diagPi, Matrix.det_fin_two_of]
  simp

private theorem fst_det_finEmbed (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ((Matrix.GeneralLinearGroup.det (finEmbed (𝓞 F) F g) : (AdeleRing (𝓞 F) F)ˣ) :
        AdeleRing (𝓞 F) F).1 = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_finEmbed]
  show adeleArch (𝓞 F) F (Matrix.det (finMat (𝓞 F) F _)) = 1
  rw [RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one]

private theorem snd_det_finEmbed_localEmbed_apply (k : GL (Fin 2) (v.adicCompletion F))
    (w : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k)) :
        (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w =
      Matrix.det ((finAdeleEval (𝓞 F) F w).mapMatrix
        (localMat (𝓞 F) F v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_finEmbed, coe_localEmbed]
  show finAdeleEval (𝓞 F) F w (adeleFin (𝓞 F) F (Matrix.det (finMat (𝓞 F) F _))) = _
  rw [RingHom.map_det, mapMatrix_fin_finMat, RingHom.map_det]

private theorem exists_mem_and_centralScalar_det_heckeGen_eq {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    ∃ w ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) =
        w * heckeGen (𝓞 F) F v * w⁻¹ * heckeGen (𝓞 F) F v := by
  obtain ⟨ϖ, hϖ0, -, hgen, -⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  refine ⟨finEmbed (𝓞 F) F
      (localEmbed (𝓞 F) F v (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))),
    finEmbed_localEmbed_mem_of_mem_integralSubgroup F v hv weylInt_mem, ?_⟩
  rw [← hgen]
  have hfold :
      finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
          (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) * diagPi ϖ hϖ0 *
            (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))⁻¹ * diagPi ϖ hϖ0)) =
        finEmbed (𝓞 F) F
            (localEmbed (𝓞 F) F v (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))) *
          finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) *
          (finEmbed (𝓞 F) F
            (localEmbed (𝓞 F) F v (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))))⁻¹ *
          finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) := by
    simp only [map_mul, map_inv]
  rw [← hfold]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hL : ((centralScalar (𝓞 F) F
        (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))) :
          AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2)
        ((Matrix.GeneralLinearGroup.det (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))) :
          (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := rfl
  have hR : ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
        (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) * diagPi ϖ hϖ0 *
          (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))⁻¹ * diagPi ϖ hϖ0)) :
            AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        localMat (𝓞 F) F v
          ((weylInt (v.adicCompletionIntegers F) (v.adicCompletion F) * diagPi ϖ hϖ0 *
            (weylInt (v.adicCompletionIntegers F) (v.adicCompletion F))⁻¹ * diagPi ϖ hϖ0 :
              GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) :
        AdeleRing (𝓞 F) F) := rfl
  rw [hL, hR, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    refine Prod.ext (fst_det_finEmbed F _) ?_
    ext w : 1
    show ((Matrix.GeneralLinearGroup.det (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))) :
        (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = localMat (𝓞 F) F v _ _ _ w
    rw [snd_det_finEmbed_localEmbed_apply]
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, det_coe_diagPi, localMat_apply_self,
        coe_weylInt_mul_diagPi_mul_inv_mul_diagPi, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · rw [mapMatrix_localMat_of_ne (𝓞 F) F v _ hw, Matrix.det_one,
        localMat_apply_of_ne (𝓞 F) F v _ _ _ hw, Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    refine Prod.ext rfl ?_
    ext w : 1
    show (0 : w.adicCompletion F) = localMat (𝓞 F) F v _ i j w
    by_cases hw : w = v
    · subst hw
      rw [localMat_apply_self, coe_weylInt_mul_diagPi_mul_inv_mul_diagPi, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ hij]
    · rw [localMat_apply_of_ne (𝓞 F) F v _ i j hw, Matrix.one_apply_ne hij]

private theorem centralScalar_mul_comm (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F a * g = g * centralScalar (𝓞 F) F a := by
  have hz : centralScalar (𝓞 F) F a ∈ Subgroup.center (AdelicGL2 (𝓞 F) F) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, rfl⟩
  exact ((Subgroup.mem_center_iff.mp hz) g).symm

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, diagOne_coe_apply,
    diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply]
  simp

private theorem det_heckeGen :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v := by
  show Matrix.GeneralLinearGroup.det (diagOne (uniformizerIdele F v)) = uniformizerIdele F v
  exact det_diagOne _

end WeylDatum
p2m_reactivate "P2MW.S_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero.TableUnitarity"

end WeylSection
p2m_reactivate "P2MW.S_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero.TableUnitarity"

private theorem realNorm_mul_inv_rpow (N : ℝ) (hN : 0 < N) (s : ℝ) : N * N⁻¹ ^ s = N ^ (1 - s) := by
  rw [Real.inv_rpow hN.le, Real.rpow_sub hN, Real.rpow_one, div_eq_mul_inv]

private theorem norm_eq_of_mul_conj_eq_ofReal_mul (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : z * starRingEnd ℂ z = (r : ℂ) * (r : ℂ)) : ‖z‖ = r := by
  have h1 : ((Complex.normSq z : ℝ) : ℂ) = ((r * r : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, h, Complex.ofReal_mul]
  have h2 : Complex.normSq z = r * r := Complex.ofReal_inj.mp h1
  have h3 : ‖z‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, h2, sq]
  exact (sq_eq_sq₀ (norm_nonneg z) hr).mp h3

private theorem arithmeticTable_of_rawRelations (N : ℕ) (hN : 0 < N) (s : ℝ) (a b : ℂ)
    (h1 : a * starRingEnd ℂ ((N : ℂ)⁻¹ * b) =
      (((N : ℝ)⁻¹ ^ s : ℝ) : ℂ) * starRingEnd ℂ a)
    (h2 : ((N : ℂ)⁻¹ * b) * starRingEnd ℂ ((N : ℂ)⁻¹ * b) =
      (((N : ℝ)⁻¹ ^ s : ℝ) : ℂ) * (((N : ℝ)⁻¹ ^ s : ℝ) : ℂ)) :
    a * starRingEnd ℂ b = (((N : ℝ) ^ (1 - s) : ℝ) : ℂ) * starRingEnd ℂ a ∧
      ‖b‖ = (N : ℝ) ^ (1 - s) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hconj : starRingEnd ℂ ((N : ℂ)⁻¹ * b) = (N : ℂ)⁻¹ * starRingEnd ℂ b := by
    rw [map_mul, map_inv₀, Complex.conj_natCast]
  have hK : (((N : ℝ) ^ (1 - s) : ℝ) : ℂ) = (N : ℂ) * (((N : ℝ)⁻¹ ^ s : ℝ) : ℂ) := by
    rw [← realNorm_mul_inv_rpow (N : ℝ) hNr s, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [hconj] at h1 h2
  refine ⟨?_, ?_⟩
  · have e : a * starRingEnd ℂ b = (N : ℂ) * (a * ((N : ℂ)⁻¹ * starRingEnd ℂ b)) := by
      rw [mul_left_comm (N : ℂ), mul_inv_cancel_left₀ hNc]
    rw [hK, e, h1]
    ring
  · refine norm_eq_of_mul_conj_eq_ofReal_mul b _ (Real.rpow_nonneg hNr.le _) ?_
    have e2 : b * starRingEnd ℂ b =
        (N : ℂ) * (N : ℂ) * (((N : ℂ)⁻¹ * b) * ((N : ℂ)⁻¹ * starRingEnd ℂ b)) := by
      rw [show (N : ℂ) * (N : ℂ) * (((N : ℂ)⁻¹ * b) * ((N : ℂ)⁻¹ * starRingEnd ℂ b)) =
          ((N : ℂ) * ((N : ℂ)⁻¹ * b)) * ((N : ℂ) * ((N : ℂ)⁻¹ * starRingEnd ℂ b)) by ring,
        mul_inv_cancel_left₀ hNc, mul_inv_cancel_left₀ hNc]
    rw [hK, e2, h2]
    ring

open AutomorphicForm NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain in
theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ) (s : ℝ)
    (hP : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y)
    (hself : P R'.toFun R'.toFun ≠ 0) :
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R'.exceptionalSet → ¬ v.asIdeal ∣ π'.level →
      π'.a v * starRingEnd ℂ (π'.b v) =
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) : ℝ) : ℂ) * starRingEnd ℂ (π'.a v) ∧
        ‖π'.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - s) := by
  intro v hv hlev

  have hU := R'.level_invariant
  dsimp only [productionPinsOf_U, HeckeEigensystem.toRawCentral_level] at hU
  obtain ⟨reps, hsys, ha⟩ := R'.hecke_eigen v hv
  dsimp only [productionPinsOf_U, productionPinsOf_gen, HeckeEigensystem.toRawCentral_level] at hsys
  dsimp only [SmoothCusp.heckeCosetSum, HeckeEigensystem.toRawCentral_a] at ha
  have hb := R'.central_eigen v hv
  dsimp only [productionPinsOf_gen, HeckeEigensystem.toRawCentral_b, HeckeEigensystem.cNorm] at hb

  obtain ⟨w, hwU, hweyl⟩ := WeylDatum.exists_mem_and_centralScalar_det_heckeGen_eq F v hlev
  have hzc := fun x =>
    WeylDatum.centralScalar_mul_comm F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) x
  have hmem := fun i => HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
  have hV : ∀ t, TableUnitarity.rt R'.toFun t ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) :=
    fun t => Submodule.subset_span (Set.mem_range_self t)

  have h1 := TableUnitarity.eigen_mul_conj_central hU hV P hP hself hmem ha hzc hb hwU hweyl
  have h2 := TableUnitarity.central_mul_conj_central hU hV P hP hself hzc hb hwU hweyl

  rw [WeylDatum.det_heckeGen F v, NumberField.TateGlobal.ideleNorm_uniformizerIdele F v] at h1 h2
  exact arithmeticTable_of_rawRelations (Ideal.absNorm v.asIdeal)
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) s (π'.a v) (π'.b v) h1 h2

end S_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero (solution)
