-- Prove2me | solution 1 for AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/531ba92c-5539-5d8c-8087-c9847d092539

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

open HeckeIntegralSeam LocalGL2 AdelicDock

namespace Ws20
namespace LevelBot

def lowerRowOne (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh0]; ring
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh1]; ring
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    have hmul : (g : Matrix (Fin 2) (Fin 2) R) * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) hmul
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) hmul
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, zero_mul, one_mul, zero_add,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.one_apply_eq] at h10 h11
    exact ⟨h10, h11⟩

theorem mem_lowerRowOne_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    g ∈ lowerRowOne R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := Iff.rfl

variable (F : Type) [Field F] [NumberField F]

noncomputable def mirabolicFin : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (lowerRowOne (FiniteAdeleRing (𝓞 F) F)).comap (glFin (𝓞 F) F)

variable {F}

theorem mem_mirabolicFin_iff (g : AdelicGL2 (𝓞 F) F) :
    g ∈ mirabolicFin F ↔ ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0 ∧
      ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 :=
  Iff.rfl

theorem eq_zero_of_mem_idealBall_bot {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∈ idealBall (𝓞 F) F ⊥) : x = 0 := by
  refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
  have h := hx w
  rw [idealBound_bot, le_zero_iff, map_eq_zero] at h
  rw [h]; rfl

variable (F)

theorem levelOne_bot_inf_le_mirabolicFin :
    levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F ≤ mirabolicFin F := by
  intro k hk
  obtain ⟨hk1, -⟩ := Subgroup.mem_inf.mp hk
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1
  obtain ⟨⟨⟨-, h10⟩, h11⟩, -⟩ := hk1
  exact (mem_mirabolicFin_iff k).mpr ⟨eq_zero_of_mem_idealBall_bot h10, sub_eq_zero.mp (eq_zero_of_mem_idealBall_bot h11)⟩

theorem levelOne_bot_inf_le_top_inf :
    levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  intro k hk
  obtain ⟨hk1, hkf⟩ := Subgroup.mem_inf.mp hk
  refine Subgroup.mem_inf.mpr ⟨?_, hkf⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1 ⊢
  have hball : ∀ {x : FiniteAdeleRing (𝓞 F) F}, x ∈ idealBall (𝓞 F) F ⊥ → x ∈ idealBall (𝓞 F) F ⊤ :=
    fun hx => by rw [eq_zero_of_mem_idealBall_bot hx]; exact zero_mem_idealBall ⊤
  exact ⟨⟨⟨hk1.1.toIsLevelZeroMatrix.integral, hball hk1.1.lowerLeft⟩, hball hk1.1.lowerRight⟩,
    ⟨⟨hk1.2.toIsLevelZeroMatrix.integral, hball hk1.2.lowerLeft⟩, hball hk1.2.lowerRight⟩⟩

theorem mem_levelOne_bot_inf_of_mem_top_of_mem_mirabolicFin {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F) (hm : k ∈ mirabolicFin F) :
    k ∈ levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨hk1, hkf⟩ := Subgroup.mem_inf.mp hk
  have hm' : k⁻¹ ∈ mirabolicFin F := inv_mem hm
  rw [mem_mirabolicFin_iff] at hm hm'
  rw [map_inv] at hm'
  refine Subgroup.mem_inf.mpr ⟨?_, hkf⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1 ⊢
  refine ⟨⟨⟨hk1.1.toIsLevelZeroMatrix.integral, ?_⟩, ?_⟩, ⟨⟨hk1.2.toIsLevelZeroMatrix.integral, ?_⟩, ?_⟩⟩
  · rw [hm.1]; exact zero_mem_idealBall ⊥
  · rw [hm.2, sub_self]; exact zero_mem_idealBall ⊥
  · rw [hm'.1]; exact zero_mem_idealBall ⊥
  · rw [hm'.2, sub_self]; exact zero_mem_idealBall ⊥

theorem heckeGen_mem_mirabolicFin (v : HeightOneSpectrum (𝓞 F)) : heckeGen (𝓞 F) F v ∈ mirabolicFin F := by
  rw [mem_mirabolicFin_iff, glFin_apply, glFin_apply]
  refine ⟨?_, ?_⟩
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw
      show (((heckeGenAt (𝓞 F) F w (uniformizerUnit F w) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 w = _
      rw [heckeGenAt_snd_apply_self]; rfl
    · show (((heckeGenAt (𝓞 F) F v (uniformizerUnit F v) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 w = _
      rw [heckeGenAt_snd_apply_of_ne _ hw, Matrix.one_apply_ne (by decide)]; rfl
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw
      show (((heckeGenAt (𝓞 F) F w (uniformizerUnit F w) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 w = _
      rw [heckeGenAt_snd_apply_self]; rfl
    · show (((heckeGenAt (𝓞 F) F v (uniformizerUnit F v) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 w = _
      rw [heckeGenAt_snd_apply_of_ne _ hw, Matrix.one_apply_eq]; rfl

theorem finEmbed_localEmbed_mem_mirabolicFin (v : HeightOneSpectrum (𝓞 F)) (m : GL (Fin 2) (v.adicCompletion F))
    (h10 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0)
    (h11 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 1) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) ∈ mirabolicFin F := by
  rw [mem_mirabolicFin_iff, glFin_finEmbed, coe_localEmbed]
  refine ⟨?_, ?_⟩
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [localMat_apply_self, h10]; rfl
    · rw [localMat_apply_of_ne _ _ _ _ _ _ hw, Matrix.one_apply_ne (by decide)]; rfl
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [localMat_apply_self, h11]; rfl
    · rw [localMat_apply_of_ne _ _ _ _ _ _ hw, Matrix.one_apply_eq]; rfl

theorem doubleCoset_mono {G : Type*} [Group G] {U U' : Subgroup G} (h : U ≤ U') (g : G) :
    HeckePair.doubleCoset U g ⊆ HeckePair.doubleCoset U' g := by
  intro x hx
  obtain ⟨u, hu, w, hw, hx⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u, h hu, w, h hw, hx⟩

theorem doubleCoset_subset_of_le {G : Type*} [Group G] {U M : Subgroup G} (h : U ≤ M) {g : G} (hg : g ∈ M) :
    HeckePair.doubleCoset U g ⊆ M := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact M.mul_mem (M.mul_mem (h hu) hg) (h hw)

theorem localRepInf_inv_entries {v : HeightOneSpectrum (𝓞 F)} (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0) :
    (((localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
    (((localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)⁻¹ := by
  set M := (((localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) with hM
  have hmul : M * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
    rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [coe_localRepInf] at hmul
  have h10 := congrArg (fun X : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => X 1 0) hmul
  have h11 := congrArg (fun X : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => X 1 1) hmul
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_eq, mul_one, mul_zero, add_zero, zero_add] at h10 h11
  exact ⟨h10, eq_inv_of_mul_eq_one_left h11⟩

end Ws20.LevelBot

open Ws20.LevelBot in
theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ c := by
  classical
  rintro ⟨reps, hsys, -⟩
  obtain ⟨ϖ, hϖ0, hϖ1, -, sec, -, hsysAll⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  have hndvd : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 F)) := fun h =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
  have htop := hsysAll ⊤ hndvd

  have claimA : ∀ i, ∃ cc : 𝓞 F ⧸ v.asIdeal,
      (QuotientGroup.mk (reps i) : AdelicGL2 (𝓞 F) F ⧸ (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F))
        = QuotientGroup.mk (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec cc))))) := by
    intro i
    have hyb := hsys.mem_doubleCoset i
    have hyt : reps i ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) :=
      doubleCoset_mono (levelOne_bot_inf_le_top_inf F) _ hyb
    have hyM : reps i ∈ mirabolicFin F :=
      doubleCoset_subset_of_le (levelOne_bot_inf_le_mirabolicFin F) (heckeGen_mem_mirabolicFin F v) hyb
    obtain ⟨j, hj⟩ := htop.covers (reps i) hyt
    have hk := QuotientGroup.eq.mp hj.symm

    cases j with
    | none =>
      exfalso
      simp only [Option.elim] at hk
      obtain ⟨hk1, -⟩ := Subgroup.mem_inf.mp hk
      rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1
      have hint := hk1.1.toIsLevelZeroMatrix.integral 1 1

      obtain ⟨hI10, hI11⟩ := localRepInf_inv_entries (F := F) ϖ hϖ0
      have hy11 : ((glFin (𝓞 F) F (reps i) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 := ((mem_mirabolicFin_iff _).mp hyM).2
      have hentry : ((glFin (𝓞 F) F ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0)))⁻¹ * reps i) :
            GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v
          = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)⁻¹ := by
        rw [map_mul, map_inv, glFin_finEmbed, ← map_inv, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          coe_localEmbed, coe_add_apply, coe_mul_apply, coe_mul_apply, localMat_apply_self, localMat_apply_self,
          hI10, hI11, hy11, zero_mul, zero_add, coe_one_apply, mul_one]
      have hmem := hint v
      rw [hentry, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at hmem
      have hval : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ) := hϖ1
      rw [hval, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
      omega
    | some cc =>
      refine ⟨cc, ?_⟩
      simp only [Option.elim] at hk
      have hkM : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec cc)))))⁻¹ * reps i ∈ mirabolicFin F := by
        refine (mirabolicFin F).mul_mem (inv_mem ?_) hyM
        refine finEmbed_localEmbed_mem_mirabolicFin F v _ ?_ ?_
        · rw [coe_localRepSome]; rfl
        · rw [coe_localRepSome]; rfl
      exact (QuotientGroup.eq.mpr (mem_levelOne_bot_inf_of_mem_top_of_mem_mirabolicFin F hk hkM)).symm

  choose f hf using claimA
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : AdelicGL2 (𝓞 F) F ⧸ (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F))
      = QuotientGroup.mk (reps j)
    rw [hf i, hf j, hij]
  have hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (hcard ▸ hN)
  have hle := Nat.card_le_card_of_injective f hfinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at hle
  omega

end S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
end P2MW
export P2MW.S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup (solution)
