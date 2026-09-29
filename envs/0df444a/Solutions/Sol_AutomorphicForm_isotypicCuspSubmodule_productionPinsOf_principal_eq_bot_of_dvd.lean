-- Prove2me | solution 1 for AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/376bb8ea-6fce-5505-bfe2-b693a04f58e8

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd

set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd.AutomorphicForm"
open NumberField.AdelicLevel LocalGL2 HeckeIntegralSeam AdelicDock

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 CarrierPins productionPinsOf HeckeEigensystem isotypicCuspSubmodule isotypicCuspSubmodule_eq_bot_iff finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff"
namespace PrincipalLevelVanishing
p2m_open "AutomorphicForm"

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

private theorem isLocalLevelOne_top {N : Ideal (𝓞 F)}
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hm : IsLocalLevelOne (𝓞 F) F v N m) :
    IsLocalLevelOne (𝓞 F) F v ⊤ m := by
  refine ⟨hm.integral, ?_, ?_⟩
  · rw [idealBound_top]
    exact hm.lowerLeft.trans (idealBound_le_one N v)
  · rw [idealBound_top]
    exact hm.lowerRight.trans (idealBound_le_one N v)

private theorem mem_localLevelOne_top {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v N) : k ∈ localLevelOne (𝓞 F) F v ⊤ := by
  rw [mem_localLevelOne_iff] at hk ⊢
  exact ⟨isLocalLevelOne_top F v hk.1, isLocalLevelOne_top F v hk.2⟩

private theorem mem_top_of_mem {N : Ideal (𝓞 F)} {g : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hg : g ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    g ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨harch, hfin⟩ := components_of_mem_U F hg
  exact mem_U_of_components F harch fun w => mem_localLevelOne_top F w (hfin w)

private theorem mem_doubleCoset_top {N : Ideal (𝓞 F)} {t x : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) t) :
    x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F) t := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr
    ⟨u, mem_top_of_mem F hu, u', mem_top_of_mem F hu', rfl⟩

private theorem not_dvd_top : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 F)) := fun h =>
  v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))

private theorem exp_neg_one_lt_one : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by norm_num)

private theorem idealBound_le_of_dvd {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N) :
    idealBound (𝓞 F) N v ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hN : N = ⊥
  · rw [hN, idealBound_bot]
    exact zero_le'
  · rw [idealBound_of_ne_bot hN, WithZero.exp_le_exp]
    have h1 : (Associates.mk v.asIdeal).count (Associates.mk N).factors ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd (show N ≠ 0 from hN) v.irreducible).mpr hv
    omega

private theorem val_add_eq_of_lt {x y : v.adicCompletion F} (h : Valued.v x < Valued.v y) :
    Valued.v (x + y) = Valued.v y := by
  refine le_antisymm ((Valuation.map_add _ x y).trans (max_le h.le le_rfl)) ?_
  have h2 : Valued.v y ≤ max (Valued.v (x + y)) (Valued.v x) := by
    have h3 := Valuation.map_add (Valued.v : Valuation (v.adicCompletion F) _) (x + y) (-x)
    have hxy : x + y + -x = y := by ring
    rwa [hxy, Valuation.map_neg] at h3
  rcases le_max_iff.mp h2 with h3 | h3
  · exact h3
  · exact absurd h3 (not_le.mpr h)

private theorem val_lowerLeft_lt_one {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hm : IsLocalLevelOne (𝓞 F) F v N m) :
    Valued.v (m 1 0) < 1 :=
  lt_of_le_of_lt (hm.lowerLeft.trans (idealBound_le_of_dvd F v hv)) exp_neg_one_lt_one

private theorem val_lowerRight_eq_one {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hm : IsLocalLevelOne (𝓞 F) F v N m) :
    Valued.v (m 1 1) = 1 := by
  have hlt : Valued.v (m 1 1 - 1) < Valued.v (1 : v.adicCompletion F) := by
    rw [Valuation.map_one]
    exact lt_of_le_of_lt (hm.lowerRight.trans (idealBound_le_of_dvd F v hv)) exp_neg_one_lt_one
  have h := val_add_eq_of_lt F v hlt
  rwa [sub_add_cancel, Valuation.map_one] at h

private theorem val_integral_le_one {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v x ≤ 1 :=
  (mem_adicCompletionIntegers _ _ _).mp hx

section Local

variable (ϖ : v.adicCompletionIntegers F)
  (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)

private theorem conj_apply_one_zero (k : GL (Fin 2) (v.adicCompletion F)) :
    (((diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
      = (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
          * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi_inv, coe_diagPi]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem conj_apply_one_one (k : GL (Fin 2) (v.adicCompletion F)) :
    (((diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi_inv, coe_diagPi]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem mul_diagPi_mul_apply_one_one (k k' : GL (Fin 2) (v.adicCompletion F)) :
    ((k * diagPi ϖ hϖ0 * k' : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
            * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ
            * (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1
        + (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
            * (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem localRepInf_mul_apply_one_one (g : GL (Fin 2) (v.adicCompletion F)) :
    ((localRepInf ϖ hϖ0 * g : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ
          * (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
  rw [Units.val_mul, coe_localRepInf]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem isLocalLevelOne_conj {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : IsLocalLevelOne (𝓞 F) F v N (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
    (hint : ∀ i j, (((diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) :
    IsLocalLevelOne (𝓞 F) F v N
      (((diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
  refine ⟨hint, ?_, ?_⟩
  · rw [conj_apply_one_zero, Valuation.map_mul]
    calc Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)
          * Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)
        ≤ Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) * 1 :=
          mul_le_mul' le_rfl (val_integral_le_one F v ϖ.2)
      _ = Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) := mul_one _
      _ ≤ idealBound (𝓞 F) N v := hk.lowerLeft
  · rw [conj_apply_one_one]
    exact hk.lowerRight

private theorem conj_mem_localLevelOne {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v N)
    (htop : (diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 ∈ localLevelOne (𝓞 F) F v ⊤) :
    (diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff] at hk htop ⊢
  have hinv : ((diagPi ϖ hϖ0)⁻¹ * k * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F))⁻¹
      = (diagPi ϖ hϖ0)⁻¹ * k⁻¹ * diagPi ϖ hϖ0 := by
    group
  rw [hinv] at htop ⊢
  exact ⟨isLocalLevelOne_conj F v ϖ hϖ0 hk.1 htop.1.integral,
    isLocalLevelOne_conj F v ϖ hϖ0 hk.2 htop.2.integral⟩

end Local

section Adelic

variable (ϖ : v.adicCompletionIntegers F)
  (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)

private theorem mk_eq_of_mk_top_eq {N : Ideal (𝓞 F)} {x y : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
    (hy : y ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
    (hxy : (QuotientGroup.mk x : _ ⧸ (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F))
      = QuotientGroup.mk y) :
    (QuotientGroup.mk x : _ ⧸ (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F))
      = QuotientGroup.mk y := by
  obtain ⟨u₁, hu₁, u₁', hu₁', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨u₂, hu₂, u₂', hu₂', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
  rw [QuotientGroup.eq] at hxy ⊢
  obtain ⟨z, hzU, hz⟩ : ∃ z ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, z = u₁⁻¹ * u₂ :=
    ⟨_, mul_mem (inv_mem hu₁) hu₂, rfl⟩
  have hrel : (u₁ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₁')⁻¹
        * (u₂ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₂')
      = u₁'⁻¹ * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))) * u₂' := by
    rw [hz]
    group
  rw [hrel] at hxy ⊢
  have hmtop : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
      ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
    have h1 := mul_mem (mul_mem (mem_top_of_mem F hu₁') hxy) (inv_mem (mem_top_of_mem F hu₂'))
    have h2 : u₁' * (u₁'⁻¹ * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))) * u₂') * u₂'⁻¹
        = (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) := by
      group
    rwa [h2] at h1
  have hmN : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
      ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    obtain ⟨hzarch, hzfin⟩ := components_of_mem_U F hzU
    obtain ⟨-, hmfin⟩ := components_of_mem_U F hmtop
    refine mem_U_of_components F ?_ fun w => ?_
    · simp only [map_mul, map_inv, glArch_finEmbed, hzarch]
      simp
    · by_cases hw : w = v
      · subst hw
        have e : finComponent (𝓞 F) F w (glFin (𝓞 F) F
              ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F w (diagPi ϖ hϖ0)))⁻¹ * z
                * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F w (diagPi ϖ hϖ0))))
            = (diagPi ϖ hϖ0)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F z)
                * diagPi ϖ hϖ0 := by
          simp only [map_mul, map_inv, comp_self]
        have hmw := hmfin w
        rw [e] at hmw ⊢
        exact conj_mem_localLevelOne F w ϖ hϖ0 (hzfin w) hmw
      · have e : finComponent (𝓞 F) F w (glFin (𝓞 F) F
              ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
                * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
            = finComponent (𝓞 F) F w (glFin (𝓞 F) F z) := by
          simp only [map_mul, map_inv, comp_of_ne F v _ hw]
          simp
        rw [e]
        exact hzfin w
  exact mul_mem (mul_mem (inv_mem hu₁') hmN) hu₂'

private theorem mk_top_ne_mk_inf {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    (hval : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    {x : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))) :
    (QuotientGroup.mk x : _ ⧸ (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F))
      ≠ QuotientGroup.mk (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0))) := by
  intro heq
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨g, hg, hxg⟩ : ∃ g ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F,
      u₁ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₂
        = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0)) * g :=
    ⟨_, QuotientGroup.eq.mp heq.symm, by rw [mul_inv_cancel_left]⟩

  have hk₁ := ((mem_localLevelOne_iff (𝓞 F) F v _).mp ((components_of_mem_U F hu₁).2 v)).1
  have hk₂ := ((mem_localLevelOne_iff (𝓞 F) F v _).mp ((components_of_mem_U F hu₂).2 v)).1
  have hgv := ((mem_localLevelOne_iff (𝓞 F) F v _).mp ((components_of_mem_U F hg).2 v)).1
  have hcomp := congrArg (fun y => finComponent (𝓞 F) F v (glFin (𝓞 F) F y)) hxg
  simp only [map_mul, comp_self] at hcomp
  have hentry := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) =>
    (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) hcomp
  rw [mul_diagPi_mul_apply_one_one, localRepInf_mul_apply_one_one] at hentry

  have hϖle : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) ≤ 1 :=
    val_integral_le_one F v ϖ.2
  have hsmall : Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
        * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ
        * (finComponent (𝓞 F) F v (glFin (𝓞 F) F u₂) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1) < 1 := by
    rw [Valuation.map_mul, Valuation.map_mul]
    calc _ ≤ Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl hϖle) (val_integral_le_one F v (hk₂.integral 0 1))
      _ = Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) := by rw [mul_one, mul_one]
      _ < 1 := val_lowerLeft_lt_one F v hv hk₁
  have hbig : Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
        * (finComponent (𝓞 F) F v (glFin (𝓞 F) F u₂) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) = 1 := by
    rw [Valuation.map_mul, val_lowerRight_eq_one F v hv hk₁, val_lowerRight_eq_one F v hv hk₂,
      mul_one]
  have hleft := val_add_eq_of_lt F v (hsmall.trans_eq hbig.symm)
  rw [hbig, hentry, Valuation.map_mul] at hleft

  have hval' : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)
      = WithZero.exp (-1 : ℤ) := hval
  have hright : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)
      * Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) < 1 := by
    calc _ ≤ Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) * 1 :=
          mul_le_mul' le_rfl (val_integral_le_one F v (hgv.integral 1 1))
      _ = WithZero.exp (-1 : ℤ) := by rw [mul_one, hval']
      _ < 1 := exp_neg_one_lt_one
  rw [hleft] at hright
  exact lt_irrefl _ hright

end Adelic

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

section Weyl

private theorem wc_inv : (wc F v)⁻¹ = wc F v :=
  inv_eq_of_mul_eq_one_right (wc_mul_self F v)

private theorem wc_coe :
    ((wc F v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![0, 1; 1, 0] := by
  ext i j
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;> rfl

private theorem wc_conj_coe (m : GL (Fin 2) (v.adicCompletion F)) :
    (((wc F v)⁻¹ * m * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1,
            (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0;
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1,
            (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0] := by
  rw [wc_inv, Units.val_mul, Units.val_mul, wc_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem wc_conj_apply_one_zero (m : GL (Fin 2) (v.adicCompletion F)) :
    (((wc F v)⁻¹ * m * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
      = (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 := by
  rw [wc_conj_coe]
  simp

private theorem wc_conj_apply_one_one (m : GL (Fin 2) (v.adicCompletion F)) :
    (((wc F v)⁻¹ * m * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 := by
  rw [wc_conj_coe]
  simp

private theorem val_upperRight_le {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hkw : IsLocalLevelOne (𝓞 F) F v N
      (((wc F v)⁻¹ * k * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1) ≤ idealBound (𝓞 F) N v := by
  have h := hkw.lowerLeft
  rwa [wc_conj_apply_one_zero] at h

private theorem val_upperLeft_sub_one_le {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hkw : IsLocalLevelOne (𝓞 F) F v N
      (((wc F v)⁻¹ * k * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 - 1) ≤ idealBound (𝓞 F) N v := by
  have h := hkw.lowerRight
  rwa [wc_conj_apply_one_one] at h

private theorem integral_of_four {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (h00 : m 0 0 ∈ v.adicCompletionIntegers F) (h01 : m 0 1 ∈ v.adicCompletionIntegers F)
    (h10 : m 1 0 ∈ v.adicCompletionIntegers F) (h11 : m 1 1 ∈ v.adicCompletionIntegers F) :
    ∀ i j, m i j ∈ v.adicCompletionIntegers F := by
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

private theorem wc_conj_inv (k : GL (Fin 2) (v.adicCompletion F)) :
    ((wc F v)⁻¹ * k * wc F v : GL (Fin 2) (v.adicCompletion F))⁻¹ = (wc F v)⁻¹ * k⁻¹ * wc F v := by
  group

end Weyl

section Scalar

variable {N : Ideal (𝓞 F)}

private theorem val_pow_count (ϖ : v.adicCompletionIntegers F)
    (hval : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (hN : N ≠ ⊥) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)
        (ϖ ^ (Associates.mk v.asIdeal).count (Associates.mk N).factors))
      = idealBound (𝓞 F) N v := by
  have hval' : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)
      = WithZero.exp (-1 : ℤ) := hval
  rw [idealBound_of_ne_bot hN, map_pow, Valuation.map_pow, hval', ← WithZero.exp_nsmul]
  congr 1
  simp

private theorem val_pos_of_ne_zero {s : v.adicCompletion F} (hs0 : s ≠ 0) : 0 < Valued.v s :=
  zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hs0)

private theorem inv_mul_integral_of_le_bound {s : v.adicCompletionIntegers F}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) s)
      = idealBound (𝓞 F) N v)
    (hs0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) s ≠ 0)
    {b : v.adicCompletion F} (hb : Valued.v b ≤ idealBound (𝓞 F) N v) :
    (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) s)⁻¹ * b
      ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀]
  by_cases hN : N = ⊥
  · subst hN
    rw [idealBound_bot, le_zero_iff, Valuation.zero_iff] at hb
    subst hb
    simp
  · rw [← hs hN] at hb
    rw [inv_mul_eq_div]
    exact (div_le_one₀ (val_pos_of_ne_zero F v hs0)).mpr hb

private theorem val_le_bound_of_inv_mul_integral {s : v.adicCompletionIntegers F}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) s)
      = idealBound (𝓞 F) N v)
    (hs0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) s ≠ 0)
    {c : v.adicCompletion F}
    (hc : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) s)⁻¹ * c
      ∈ v.adicCompletionIntegers F)
    (hc0 : N = ⊥ → c = 0) :
    Valued.v c ≤ idealBound (𝓞 F) N v := by
  by_cases hN : N = ⊥
  · rw [hc0 hN, Valuation.map_zero]
    exact zero_le'
  · rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, inv_mul_eq_div,
      div_le_one₀ (val_pos_of_ne_zero F v hs0)] at hc
    rwa [← hs hN]

private theorem eq_zero_of_le_bound_bot {b : v.adicCompletion F}
    (hb : Valued.v b ≤ idealBound (𝓞 F) (⊥ : Ideal (𝓞 F)) v) : b = 0 := by
  rwa [idealBound_bot, le_zero_iff, Valuation.zero_iff] at hb

end Scalar

section LocalTwo

variable (σ : v.adicCompletionIntegers F)
  (hσ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ ≠ 0)

private theorem conj_apply_zero_zero (k : GL (Fin 2) (v.adicCompletion F)) :
    (((diagPi σ hσ0)⁻¹ * k * diagPi σ hσ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
      = (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 := by
  have hσ0' : (σ : v.adicCompletion F) ≠ 0 := hσ0
  rw [Units.val_mul, Units.val_mul, coe_diagPi_inv, coe_diagPi]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mul_right_comm, inv_mul_cancel₀ hσ0', one_mul]

private theorem conj_apply_zero_one (k : GL (Fin 2) (v.adicCompletion F)) :
    (((diagPi σ hσ0)⁻¹ * k * diagPi σ hσ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1
      = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)⁻¹
          * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi_inv, coe_diagPi]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem conj_inv (k : GL (Fin 2) (v.adicCompletion F)) :
    ((diagPi σ hσ0)⁻¹ * k * diagPi σ hσ0 : GL (Fin 2) (v.adicCompletion F))⁻¹
      = (diagPi σ hσ0)⁻¹ * k⁻¹ * diagPi σ hσ0 := by
  group

private theorem diagPi_comm (τ : v.adicCompletionIntegers F)
    (hτ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) τ ≠ 0) :
    diagPi σ hσ0 * diagPi τ hτ0 = diagPi τ hτ0 * diagPi σ hσ0 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diagPi, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem conj_s_mem_localLevelOne {N : Ideal (𝓞 F)}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v)
    {k : GL (Fin 2) (v.adicCompletion F)} (hk : k ∈ localLevelOne (𝓞 F) F v N)
    (hkw : (wc F v)⁻¹ * k * wc F v ∈ localLevelOne (𝓞 F) F v N) :
    (diagPi σ hσ0)⁻¹ * k * diagPi σ hσ0 ∈ localLevelOne (𝓞 F) F v N := by
  have hk' := (mem_localLevelOne_iff (𝓞 F) F v _).mp hk
  have hkw' := (mem_localLevelOne_iff (𝓞 F) F v _).mp hkw
  rw [wc_conj_inv] at hkw'
  refine conj_mem_localLevelOne F v σ hσ0 hk ?_
  refine mem_localLevelOne_of_integral F v (not_dvd_top F v) ?_ ?_
  · refine integral_of_four F v ?_ ?_ ?_ ?_
    · rw [conj_apply_zero_zero]
      exact hk'.1.integral 0 0
    · rw [conj_apply_zero_one]
      exact inv_mul_integral_of_le_bound F v hs hσ0 (val_upperRight_le F v hkw'.1)
    · rw [conj_apply_one_zero]
      exact mul_mem (hk'.1.integral 1 0) σ.2
    · rw [conj_apply_one_one]
      exact hk'.1.integral 1 1
  · rw [conj_inv]
    refine integral_of_four F v ?_ ?_ ?_ ?_
    · rw [conj_apply_zero_zero]
      exact hk'.2.integral 0 0
    · rw [conj_apply_zero_one]
      exact inv_mul_integral_of_le_bound F v hs hσ0 (val_upperRight_le F v hkw'.2)
    · rw [conj_apply_one_zero]
      exact mul_mem (hk'.2.integral 1 0) σ.2
    · rw [conj_apply_one_one]
      exact hk'.2.integral 1 1

end LocalTwo

section LocalCore

variable (ϖ : v.adicCompletionIntegers F)
  (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
  (σ : v.adicCompletionIntegers F)
  (hσ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ ≠ 0)

private theorem conj_integral {N : Ideal (𝓞 F)} {z : GL (Fin 2) (v.adicCompletion F)}
    (hz : IsLocalLevelOne (𝓞 F) F v N (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
    (hδ : IsLocalLevelOne (𝓞 F) F v N
      (((diagPi σ hσ0)⁻¹ * ((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0) * diagPi σ hσ0 :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :
    ∀ i j, (((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
  refine integral_of_four F v ?_ ?_ ?_ ?_
  · rw [conj_apply_zero_zero]
    exact hz.integral 0 0
  · have h := hδ.integral 0 1
    rw [conj_apply_zero_one] at h
    have e := mul_inv_cancel_left₀ hσ0
      ((((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0 : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1)
    rw [← e]
    exact mul_mem σ.2 h
  · rw [conj_apply_one_zero]
    exact mul_mem (hz.integral 1 0) ϖ.2
  · rw [conj_apply_one_one]
    exact hz.integral 1 1

private theorem weyl_conj_isLocalLevelOne {N : Ideal (𝓞 F)}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v)
    {z : GL (Fin 2) (v.adicCompletion F)}
    (hz : IsLocalLevelOne (𝓞 F) F v N (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
    (hzw : IsLocalLevelOne (𝓞 F) F v N
      (((wc F v)⁻¹ * z * wc F v : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
    (hδ : IsLocalLevelOne (𝓞 F) F v N
      (((diagPi σ hσ0)⁻¹ * ((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0) * diagPi σ hσ0 :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :
    IsLocalLevelOne (𝓞 F) F v N
      (((wc F v)⁻¹ * ((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0) * wc F v :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
  have hint := conj_integral F v ϖ hϖ0 σ hσ0 hz hδ
  refine ⟨?_, ?_, ?_⟩
  · rw [wc_conj_coe]
    exact integral_of_four F v (by simpa using hint 1 1) (by simpa using hint 1 0)
      (by simpa using hint 0 1) (by simpa using hint 0 0)
  · rw [wc_conj_apply_one_zero]
    have h := hδ.integral 0 1
    rw [conj_apply_zero_one] at h
    refine val_le_bound_of_inv_mul_integral F v hs hσ0 h fun hN => ?_
    rw [conj_apply_zero_one]
    have hb := val_upperRight_le F v hzw
    rw [hN] at hb
    rw [eq_zero_of_le_bound_bot F v hb, mul_zero]
  · rw [wc_conj_apply_one_one, conj_apply_zero_zero]
    exact val_upperLeft_sub_one_le F v hzw

private theorem principal_conj_of_conj_s {N : Ideal (𝓞 F)}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v)
    {z : GL (Fin 2) (v.adicCompletion F)} (hz : z ∈ localLevelOne (𝓞 F) F v N)
    (hzw : (wc F v)⁻¹ * z * wc F v ∈ localLevelOne (𝓞 F) F v N)
    (hδ : (diagPi σ hσ0)⁻¹ * ((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0) * diagPi σ hσ0
      ∈ localLevelOne (𝓞 F) F v N) :
    (diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0 ∈ localLevelOne (𝓞 F) F v N ∧
      (wc F v)⁻¹ * ((diagPi ϖ hϖ0)⁻¹ * z * diagPi ϖ hϖ0) * wc F v ∈ localLevelOne (𝓞 F) F v N := by
  have hz' := (mem_localLevelOne_iff (𝓞 F) F v _).mp hz
  have hzw' := (mem_localLevelOne_iff (𝓞 F) F v _).mp hzw
  rw [wc_conj_inv] at hzw'
  have hδ' := (mem_localLevelOne_iff (𝓞 F) F v _).mp hδ
  rw [conj_inv, conj_inv] at hδ'
  refine ⟨?_, ?_⟩
  · refine conj_mem_localLevelOne F v ϖ hϖ0 hz ?_
    refine mem_localLevelOne_of_integral F v (not_dvd_top F v)
      (conj_integral F v ϖ hϖ0 σ hσ0 hz'.1 hδ'.1) ?_
    rw [conj_inv]
    exact conj_integral F v ϖ hϖ0 σ hσ0 hz'.2 hδ'.2
  · rw [mem_localLevelOne_iff]
    refine ⟨weyl_conj_isLocalLevelOne F v ϖ hϖ0 σ hσ0 hs hz'.1 hzw'.1 hδ'.1, ?_⟩
    rw [wc_conj_inv, conj_inv]
    exact weyl_conj_isLocalLevelOne F v ϖ hϖ0 σ hσ0 hs hz'.2 hzw'.2 hδ'.2

end LocalCore

section AdelicPrincipal

variable (ϖ : v.adicCompletionIntegers F)
  (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
  (σ : v.adicCompletionIntegers F)
  (hσ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ ≠ 0)

private theorem embed_diag_comm :
    (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
      = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) := by
  have h : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
      = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) := by
    simp only [← map_mul]
    rw [diagPi_comm F v ϖ hϖ0 σ hσ0]
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem conj_s_mem_U {N : Ideal (𝓞 F)}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v)
    {p : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * p
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
      ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨harch, hfin⟩ := components_of_mem_U F (P_le_U F N hp)
  refine mem_U_of_components F ?_ fun w => ?_
  · simp only [map_mul, map_inv, glArch_finEmbed, harch]
    simp
  · by_cases hw : w = v
    · subst hw
      have e : finComponent (𝓞 F) F w (glFin (𝓞 F) F
            ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F w (diagPi σ hσ0)))⁻¹ * p
              * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F w (diagPi σ hσ0))))
          = (diagPi σ hσ0)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p) * diagPi σ hσ0 := by
        simp only [map_mul, map_inv, comp_self]
      rw [e]
      exact conj_s_mem_localLevelOne F w σ hσ0 hs (hfin w) (components_of_mem_P F hp w)
    · have e : finComponent (𝓞 F) F w (glFin (𝓞 F) F
            ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * p
              * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))))
          = finComponent (𝓞 F) F w (glFin (𝓞 F) F p) := by
        simp only [map_mul, map_inv, comp_of_ne F v _ hw]
        simp
      rw [e]
      exact hfin w

private theorem conj_s_mem_doubleCoset {N : Ideal (𝓞 F)}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v)
    {x : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hx : x ∈ HeckePair.doubleCoset (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))) :
    (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * x
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
      ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))) := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  have e : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
        * (u₁ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₂)
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
      = ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * u₁
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))
          * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))
          * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * u₂
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))) := by
    group
  rw [e, embed_diag_comm]
  exact HeckePair.mem_doubleCoset_iff.mpr
    ⟨_, conj_s_mem_U F v σ hσ0 hs hu₁, _, conj_s_mem_U F v σ hσ0 hs hu₂, rfl⟩

private theorem mk_eq_of_conj_mk_eq {N : Ideal (𝓞 F)}
    (hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v)
    {x y : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hx : x ∈ HeckePair.doubleCoset (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
    (hy : y ∈ HeckePair.doubleCoset (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
    (hxy : (QuotientGroup.mk ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * x
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))) :
          _ ⧸ (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F))
      = QuotientGroup.mk ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * y
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))) :
    (QuotientGroup.mk x : _ ⧸ (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F))
      = QuotientGroup.mk y := by
  obtain ⟨u₁, hu₁, u₁', hu₁', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨u₂, hu₂, u₂', hu₂', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
  rw [QuotientGroup.eq] at hxy ⊢
  obtain ⟨z, hzP, hz⟩ : ∃ z ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, z = u₁⁻¹ * u₂ :=
    ⟨_, mul_mem (inv_mem hu₁) hu₂, rfl⟩

  have hrel : (u₁ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₁')⁻¹
        * (u₂ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₂')
      = u₁'⁻¹ * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))) * u₂' := by
    rw [hz]
    group
  rw [hrel]

  have hconj : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
        * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))
      ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    have h1 := mul_mem (mul_mem (conj_s_mem_U F v σ hσ0 hs hu₁') hxy)
      (inv_mem (conj_s_mem_U F v σ hσ0 hs hu₂'))
    have h2 : ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * u₁'
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))
        * (((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
            * (u₁ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₁')
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
          * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
            * (u₂ * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) * u₂')
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))))
        * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * u₂'
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
        = (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
          * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
            * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)) := by
      rw [hz]
      group
    rwa [h2] at h1
  obtain ⟨-, hconjfin⟩ := components_of_mem_U F hconj
  obtain ⟨hzarch, hzfin⟩ := components_of_mem_U F (P_le_U F N hzP)

  have hv_core := principal_conj_of_conj_s F v ϖ hϖ0 σ hσ0 hs (hzfin v) (components_of_mem_P F hzP v)
    (by
      have e : finComponent (𝓞 F) F v (glFin (𝓞 F) F
            ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹
              * ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
                * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))
              * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))))
          = (diagPi σ hσ0)⁻¹ * ((diagPi ϖ hϖ0)⁻¹ * finComponent (𝓞 F) F v (glFin (𝓞 F) F z)
              * diagPi ϖ hϖ0) * diagPi σ hσ0 := by
        simp only [map_mul, map_inv, comp_self]
      have h := hconjfin v
      rwa [e] at h)
  have hcomp_v : finComponent (𝓞 F) F v (glFin (𝓞 F) F
        ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
      = (diagPi ϖ hϖ0)⁻¹ * finComponent (𝓞 F) F v (glFin (𝓞 F) F z) * diagPi ϖ hϖ0 := by
    simp only [map_mul, map_inv, comp_self]
  have hcomp_w : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → finComponent (𝓞 F) F w (glFin (𝓞 F) F
        ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))))
      = finComponent (𝓞 F) F w (glFin (𝓞 F) F z) := by
    intro w hw
    simp only [map_mul, map_inv, comp_of_ne F v _ hw]
    simp

  have hmU : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
      ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F ?_ fun w => ?_
    · simp only [map_mul, map_inv, glArch_finEmbed, hzarch]
      simp
    · by_cases hw : w = v
      · subst hw
        rw [hcomp_v]
        exact hv_core.1
      · rw [hcomp_w w hw]
        exact hzfin w

  have hmP : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))⁻¹ * z
        * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0))
      ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_P_of_components F hmU fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [hcomp_v]
      exact hv_core.2
    · rw [hcomp_w w hw]
      exact components_of_mem_P F hzP w
  exact mul_mem (mul_mem (inv_mem hu₁') hmP) hu₂'

end AdelicPrincipal

private
theorem card_le_absNorm_of_isHeckeCosetSystem_principal_of_dvd {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    {ι : Type} [Fintype ι] {reps : ι → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) reps) :
    Fintype.card ι ≤ Ideal.absNorm v.asIdeal := by
  obtain ⟨ϖ, hϖ0, hval, hgen, sec, -, hM⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  have S := hM ⊤ (not_dvd_top F v)
  rw [← hgen] at hsys S

  set σ : v.adicCompletionIntegers F := ϖ ^ (Associates.mk v.asIdeal).count (Associates.mk N).factors
    with hσ
  have hσ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ ≠ 0 := by
    rw [hσ, map_pow]
    exact pow_ne_zero _ hϖ0
  have hs : N ≠ ⊥ → Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) σ)
      = idealBound (𝓞 F) N v := fun hN => val_pow_count F v ϖ hval hN

  have hlab : ∀ i, ∃ c : 𝓞 F ⧸ v.asIdeal,
      (QuotientGroup.mk ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0)))⁻¹ * reps i
          * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi σ hσ0))) :
            _ ⧸ (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F))
        = QuotientGroup.mk (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c))))) := by
    intro i
    have hi := conj_s_mem_doubleCoset F v ϖ hϖ0 σ hσ0 hs (hsys.mem_doubleCoset i)
    obtain ⟨j, hj⟩ := S.covers _ (mem_doubleCoset_top F hi)
    cases j with
    | none => exact absurd hj (mk_top_ne_mk_inf F v ϖ hϖ0 hv hval hi)
    | some c => exact ⟨c, hj⟩
  choose lab hlab using hlab
  have hinj : Function.Injective lab := by
    intro i i' hii'
    refine hsys.mk_injective ?_
    refine mk_eq_of_conj_mk_eq F v ϖ hϖ0 σ hσ0 hs (hsys.mem_doubleCoset i) (hsys.mem_doubleCoset i') ?_
    exact mk_eq_of_mk_top_eq F v ϖ hϖ0
      (conj_s_mem_doubleCoset F v ϖ hϖ0 σ hσ0 hs (hsys.mem_doubleCoset i))
      (conj_s_mem_doubleCoset F v ϖ hϖ0 σ hσ0 hs (hsys.mem_doubleCoset i'))
      (by rw [hlab i, hlab i', hii'])
  have habs : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp habs
  haveI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  calc Fintype.card ι ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := Fintype.card_le_of_injective lab hinj
    _ = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private
theorem not_isHeckeCosetSystem_principal_fin_of_dvd {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F) :
    ¬ IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) reps := by
  intro hsys
  have h := card_le_absNorm_of_isHeckeCosetSystem_principal_of_dvd F v hv hsys
  rw [Fintype.card_fin] at h
  omega

section Vanishing

private
theorem isotypicCuspSubmodule_eq_bot_of_dvd_principal (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N)
    (hU : pins.U N = principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (hgen : pins.gen v = heckeGen (𝓞 F) F v) :
    isotypicCuspSubmodule F pins ξ N S Φ = ⊥ := by
  rw [isotypicCuspSubmodule_eq_bot_iff]
  intro φ hφ
  obtain ⟨reps, hsys, -⟩ := hφ.hecke_eigen v hvS
  rw [hU, hgen] at hsys
  exact absurd hsys (not_isHeckeCosetSystem_principal_fin_of_dvd F v hv reps)

private
theorem isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ :=
  isotypicCuspSubmodule_eq_bot_of_dvd_principal F v _ ξ N S Φ hvS hv rfl rfl

end Vanishing

end AutomorphicForm.PrincipalLevelVanishing

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ :=
  AutomorphicForm.PrincipalLevelVanishing.isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
    F v Dset B ξ N S Φ hvS hv

#print axioms solution

end S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd
end P2MW
export P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_principal_eq_bot_of_dvd (solution)
