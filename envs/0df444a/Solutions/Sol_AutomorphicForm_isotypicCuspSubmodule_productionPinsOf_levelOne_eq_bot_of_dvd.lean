-- Prove2me | solution 1 for AutomorphicForm.isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1bb7b408-f494-5a9c-a5fc-56620693471f

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
p2m_open "NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd.AutomorphicForm"
open NumberField.AdelicLevel LocalGL2 HeckeIntegralSeam AdelicDock

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 CarrierPins productionPinsOf HeckeEigensystem isotypicCuspSubmodule isotypicCuspSubmodule_eq_bot_iff finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff"
namespace LevelOneHeckeIndex
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

private
theorem card_le_absNorm_of_isHeckeCosetSystem_levelOne_of_dvd {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    {ι : Type} [Fintype ι] {reps : ι → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) reps) :
    Fintype.card ι ≤ Ideal.absNorm v.asIdeal := by
  obtain ⟨ϖ, hϖ0, hval, hgen, sec, -, hM⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  have S := hM ⊤ (not_dvd_top F v)
  rw [← hgen] at hsys S

  have hlab : ∀ i, ∃ c : 𝓞 F ⧸ v.asIdeal,
      (QuotientGroup.mk (reps i) : _ ⧸ (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F))
        = QuotientGroup.mk (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c))))) := by
    intro i
    have hi := hsys.mem_doubleCoset i
    obtain ⟨j, hj⟩ := S.covers _ (mem_doubleCoset_top F hi)
    cases j with
    | none => exact absurd hj (mk_top_ne_mk_inf F v ϖ hϖ0 hv hval hi)
    | some c => exact ⟨c, hj⟩
  choose lab hlab using hlab
  have hinj : Function.Injective lab := by
    intro i i' hii'
    refine hsys.mk_injective ?_
    exact mk_eq_of_mk_top_eq F v ϖ hϖ0 (hsys.mem_doubleCoset i) (hsys.mem_doubleCoset i')
      (by rw [hlab i, hlab i', hii'])
  have habs : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp habs
  haveI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  calc Fintype.card ι ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := Fintype.card_le_of_injective lab hinj
    _ = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private
theorem not_isHeckeCosetSystem_levelOne_fin_of_dvd {N : Ideal (𝓞 F)} (hv : v.asIdeal ∣ N)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F) :
    ¬ IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) reps := by
  intro hsys
  have h := card_le_absNorm_of_isHeckeCosetSystem_levelOne_of_dvd F v hv hsys
  rw [Fintype.card_fin] at h
  omega

private
theorem isotypicCuspSubmodule_eq_bot_of_dvd_levelOne (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N)
    (hU : pins.U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (hgen : pins.gen v = heckeGen (𝓞 F) F v) :
    isotypicCuspSubmodule F pins ξ N S Φ = ⊥ := by
  rw [isotypicCuspSubmodule_eq_bot_iff]
  intro φ hφ
  obtain ⟨reps, hsys, -⟩ := hφ.hecke_eigen v hvS
  rw [hU, hgen] at hsys
  exact absurd hsys (not_isHeckeCosetSystem_levelOne_fin_of_dvd F v hv reps)

private
theorem isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd' (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ :=
  isotypicCuspSubmodule_eq_bot_of_dvd_levelOne F v _ ξ N S Φ hvS hv rfl rfl

end AutomorphicForm.LevelOneHeckeIndex

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (Dset : Set (AdelicGL2 (𝓞 F) F))
    (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F Dset (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (hvS : v ∉ S) (hv : v.asIdeal ∣ N) :
    isotypicCuspSubmodule F
      (productionPinsOf F Dset (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ N S Φ = ⊥ :=
  AutomorphicForm.LevelOneHeckeIndex.isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd'
    F v Dset B ξ N S Φ hvS hv

end S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd
end P2MW
export P2MW.S_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd (solution)
