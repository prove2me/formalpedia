-- Prove2me | solution 1 for AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2a4effa1-ff4f-5af6-a375-af721039a7f5

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

namespace P2mS28R9

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem idealBound_mono {N N' : Ideal R} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N' v ≤ idealBound R N v := by
  have hN0 : N ≠ ⊥ := fun h => hN'0 (le_bot_iff.mp (h ▸ hN))
  rw [idealBound_of_ne_bot hN'0, idealBound_of_ne_bot hN0, WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  refine Associates.count_le_count_of_le ?_ ?_ ?_
  · exact Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
  · exact (Associates.irreducible_mk).mpr v.irreducible
  · exact Associates.mk_le_mk_of_dvd (Ideal.dvd_iff_le.mpr hN)

theorem idealBall_mono {N N' : Ideal R} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥) :
    idealBall R K N' ⊆ idealBall R K N :=
  fun _ hx v => (hx v).trans (idealBound_mono hN hN'0 v)

theorem isLevelOneMatrix_mono {N N' : Ideal R} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥)
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)} (h : IsLevelOneMatrix R K N' m) :
    IsLevelOneMatrix R K N m where
  integral := h.integral
  lowerLeft := idealBall_mono hN hN'0 h.lowerLeft
  lowerRight := idealBall_mono hN hN'0 h.lowerRight

theorem levelOne_mono {N N' : Ideal R} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥) :
    levelOne R K N' ≤ levelOne R K N := by
  intro g hg
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hg ⊢
  exact ⟨isLevelOneMatrix_mono hN hN'0 hg.1, isLevelOneMatrix_mono hN hN'0 hg.2⟩

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    {reps : ι → G} (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (e : κ ≃ ι) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset k := h.mem_doubleCoset (e k)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective k k' hkk' := e.injective (h.mk_injective (by simpa using hkk'))

end P2mS28R9

open P2mS28R9 in
theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    {N N' : Ideal (𝓞 F)} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥)
    {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS' : S ⊆ S')
    (hS' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → ¬ v.asIdeal ∣ N')
    (Ψ : HeckeEigensystem F ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ) :
    IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N' S' Ψ φ := by
  classical

  have hU : levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
    inf_le_inf_right _ (levelOne_mono hN hN'0)
  refine ⟨hφ.smoothCusp, hφ.continuous, ?_, ?_, ?_⟩
  · intro g u hu
    exact hφ.level_invariant g u (hU hu)
  · intro v hvS'
    have hvS : v ∉ S := fun h => hvS' (hSS' h)
    have hvN' : ¬ v.asIdeal ∣ N' := hS' v hvS'
    have hvN : ¬ v.asIdeal ∣ N := fun h => hvN' (h.trans (Ideal.dvd_iff_le.mpr hN))

    obtain ⟨reps₀, hsys₀, hsum₀⟩ := hφ.hecke_eigen v hvS

    obtain ⟨ϖ, hϖ0, -, -, sec, -, hfam⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hcard : Fintype.card (Option (𝓞 F ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
      rw [Fintype.card_option, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    let e : Fin (Ideal.absNorm v.asIdeal + 1) ≃ Option (𝓞 F ⧸ v.asIdeal) :=
      (Fintype.equivFinOfCardEq hcard).symm
    set fam := fun i : Option (𝓞 F ⧸ v.asIdeal) =>
      AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v
        (i.elim (LocalGL2.localRepInf ϖ hϖ0)
          (fun c => LocalGL2.localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c))))) with hfamdef
    have hsysN : HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) (fam ∘ e) := isHeckeCosetSystem_comp_equiv (hfam N hvN) e
    have hsysN' : HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) (fam ∘ e) := isHeckeCosetSystem_comp_equiv (hfam N' hvN') e
    refine ⟨fam ∘ e, hsysN', fun g => ?_⟩
    rw [← hsum₀ g]
    exact HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys₀ hsysN hφ.level_invariant g
  · intro v hvS'
    exact hφ.central_eigen v (fun h => hvS' (hSS' h))

end S_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset
end P2MW
export P2MW.S_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset (solution)
