-- Prove2me | solution 1 for AutomorphicForm.isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/aa1e5eed-814a-52b9-8989-fb743486bc00

import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm
open scoped NumberField.PlaceTransport

noncomputable section

namespace R4SigmaKernel

section Genuine

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Dg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L :=
  M4aHerbrand.GenuineDescent.genuineDescentDatum K L

omit [NumberField K] in

theorem sigmaAdelicAct_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
  rfl

omit [NumberField K] in

theorem sigmaAdelicAct_inv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) : sigmaAdelicAct K L D σ (sigmaAdelicAct K L D σ⁻¹ g) = g := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, mul_inv_cancel, sigmaAdelicAct_one]; rfl

omit [NumberField K] in
theorem sigmaAdelicAct_apply_inv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) : sigmaAdelicAct K L D σ⁻¹ (sigmaAdelicAct K L D σ g) = g := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, inv_mul_cancel, sigmaAdelicAct_one]; rfl

theorem sigmaAdelicAct_snd (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2)
    {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w') :
    (((sigmaAdelicAct K L (Dg K L) σ g : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 w' =
      NumberField.PlaceTransport.transport σ h
        ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 w)) := by
  rw [sigmaAdelicAct_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ h

theorem sigmaAdelicAct_fst (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2)
    {u u' : InfinitePlace L} (h : σ • u = u') :
    (((sigmaAdelicAct K L (Dg K L) σ g : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 u' =
      NumberField.InfinitePlaceTransport.transport σ h
        ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 u)) := by
  rw [sigmaAdelicAct_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ h

omit [NumberField K] [NumberField L] in

theorem transport_one_matrix_apply (σ : L ≃ₐ[K] L) {u u' : InfinitePlace L} (h : σ • u = u') (i j : Fin 2) :
    NumberField.InfinitePlaceTransport.transport σ h ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j u) =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j u' := by
  rw [Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem sigmaAdelicAct_mem_finiteAdelicGL2Subgroup (σ : L ≃ₐ[K] L) {g : AdelicGL2 (𝓞 L) L}
    (hg : g ∈ finiteAdelicGL2Subgroup L) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ finiteAdelicGL2Subgroup L := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg ⊢
  have hg' : ∀ i j : Fin 2, (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1) =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := fun i j => by
    rw [← glArch_apply, hg]; rfl
  refine Units.ext (Matrix.ext fun i j => funext fun u' => ?_)
  have hu : σ • (σ⁻¹ • u') = u' := smul_inv_smul σ u'
  rw [glArch_apply, sigmaAdelicAct_fst σ g i j hu, hg', transport_one_matrix_apply σ hu i j]
  rfl

theorem sigmaAdelicAct_mem_finiteAdelicGL2Subgroup_iff (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ finiteAdelicGL2Subgroup L ↔ g ∈ finiteAdelicGL2Subgroup L := by
  refine ⟨fun h => ?_, sigmaAdelicAct_mem_finiteAdelicGL2Subgroup σ⟩
  have := sigmaAdelicAct_mem_finiteAdelicGL2Subgroup σ⁻¹ h
  rwa [sigmaAdelicAct_apply_inv] at this

omit [NumberField K] [NumberField L] in

theorem comap_le_pow_iff (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) (k : ℕ) :
    N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) ≤ w.asIdeal ^ k ↔
      N ≤ (σ • w).asIdeal ^ k := by
  constructor
  · intro h x hx
    have h1 : σ⁻¹ • x ∈ w.asIdeal ^ k := by
      apply h
      rw [Ideal.mem_comap]
      show σ • (σ⁻¹ • x) ∈ N
      rwa [smul_inv_smul]
    have h2 : σ • (σ⁻¹ • x) ∈ (σ • w).asIdeal ^ k :=
      (NumberField.PlaceTransport.smul_mem_smul_asIdeal_pow_iff σ w (σ⁻¹ • x) k).2 h1
    rwa [smul_inv_smul] at h2
  · intro h x hx
    rw [Ideal.mem_comap] at hx
    have h1 : σ • x ∈ (σ • w).asIdeal ^ k := h hx
    exact (NumberField.PlaceTransport.smul_mem_smul_asIdeal_pow_iff σ w x k).1 h1

omit [NumberField K] [NumberField L] in
theorem comap_ne_bot_iff (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) :
    N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) ≠ ⊥ ↔ N ≠ ⊥ := by
  rw [not_iff_not]
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    have : σ⁻¹ • x ∈ N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) := by
      rw [Ideal.mem_comap]
      show σ • (σ⁻¹ • x) ∈ N
      rwa [smul_inv_smul]
    rw [h, Ideal.mem_bot] at this
    have hx0 : x = σ • (σ⁻¹ • x) := (smul_inv_smul σ x).symm
    rw [hx0, this, smul_zero]
    exact Ideal.zero_mem _
  · rintro rfl
    exact Ideal.comap_bot_of_injective (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)
      (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ).injective

theorem count_eq_of_forall_iff {N N' : Ideal (𝓞 L)} (hN : N ≠ ⊥) (hN' : N' ≠ ⊥)
    (w w' : HeightOneSpectrum (𝓞 L)) (h : ∀ k : ℕ, N ≤ w.asIdeal ^ k ↔ N' ≤ w'.asIdeal ^ k) :
    (Associates.mk w.asIdeal).count (Associates.mk N).factors =
      (Associates.mk w'.asIdeal).count (Associates.mk N').factors := by
  classical
  have key : ∀ k : ℕ, k ≤ (Associates.mk w.asIdeal).count (Associates.mk N).factors ↔
      k ≤ (Associates.mk w'.asIdeal).count (Associates.mk N').factors := by
    intro k
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN) w.associates_irreducible,
      ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN') w'.associates_irreducible,
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
      Ideal.dvd_iff_le, Ideal.dvd_iff_le]
    exact h k
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

omit [NumberField K] in

theorem idealBound_comap (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) :
    idealBound (𝓞 L) (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) w =
      idealBound (𝓞 L) N (σ • w) := by
  by_cases hN : N = ⊥
  · subst hN
    rw [Ideal.comap_bot_of_injective (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)
        (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ).injective,
      idealBound_bot, idealBound_bot]
  · have hN' := (comap_ne_bot_iff σ N).2 hN
    rw [idealBound_of_ne_bot hN', idealBound_of_ne_bot hN,
      count_eq_of_forall_iff hN' hN w (σ • w) (comap_le_pow_iff σ N w)]

theorem sigmaAdelicAct_snd' (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2)
    (w' : HeightOneSpectrum (𝓞 L)) :
    (((sigmaAdelicAct K L (Dg K L) σ g : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 w' =
      NumberField.PlaceTransport.transport σ (smul_inv_smul σ w')
        ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 (σ⁻¹ • w'))) :=
  sigmaAdelicAct_snd σ g i j (smul_inv_smul σ w')

theorem isLevelOneMatrix_sigmaAdelicAct (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L)
    (hg : IsLevelOneMatrix (𝓞 L) L
      (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L))
      (glFin (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :
    IsLevelOneMatrix (𝓞 L) L N
      (glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := by
  set N' := N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) with hN'
  have hentry : ∀ (i j : Fin 2) (w' : HeightOneSpectrum (𝓞 L)),
      (glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j w' =
        NumberField.PlaceTransport.transport σ (smul_inv_smul σ w')
          ((glFin (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j (σ⁻¹ • w')) := by
    intro i j w'
    rw [glFin_apply, glFin_apply]
    exact sigmaAdelicAct_snd' σ g i j w'
  have hb : ∀ w' : HeightOneSpectrum (𝓞 L), idealBound (𝓞 L) N w' = idealBound (𝓞 L) N' (σ⁻¹ • w') := by
    intro w'; rw [hN', idealBound_comap, smul_inv_smul]
  refine ⟨⟨fun i j w' => ?_, fun w' => ?_⟩, fun w' => ?_⟩
  · rw [hentry, NumberField.PlaceTransport.transport_mem_adicCompletionIntegers_iff]
    exact hg.integral i j _
  · rw [hentry, NumberField.PlaceTransport.valued_transport, hb]
    exact hg.lowerLeft _
  · have h1 : ((glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) 1 1
        - 1) w' = NumberField.PlaceTransport.transport σ (smul_inv_smul σ w')
          (((glFin (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) 1 1 - 1) (σ⁻¹ • w')) := by
      rw [coe_sub_apply, coe_sub_apply, coe_one_apply, coe_one_apply, map_sub, map_one, hentry]
    rw [h1, NumberField.PlaceTransport.valued_transport, hb]
    exact hg.lowerRight _

theorem sigmaAdelicAct_mem_levelOne (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) {g : AdelicGL2 (𝓞 L) L}
    (hg : g ∈ levelOne (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L))) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ levelOne (𝓞 L) L N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hg ⊢
  refine ⟨isLevelOneMatrix_sigmaAdelicAct σ N g hg.1, ?_⟩
  rw [← map_inv, ← map_inv]
  have h2 := hg.2
  rw [← map_inv] at h2
  exact isLevelOneMatrix_sigmaAdelicAct σ N g⁻¹ h2

omit [NumberField K] [NumberField L] in

theorem comap_comap_inv (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) :
    (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)).comap
        (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ⁻¹ : 𝓞 L →+* 𝓞 L) = N := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  show σ • (σ⁻¹ • x) ∈ N ↔ x ∈ N
  rw [smul_inv_smul]

theorem sigmaAdelicAct_mem_levelOne_iff (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ levelOne (𝓞 L) L N ↔
      g ∈ levelOne (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) := by
  refine ⟨fun h => ?_, sigmaAdelicAct_mem_levelOne σ N⟩
  have h' : sigmaAdelicAct K L (Dg K L) σ g ∈ levelOne (𝓞 L) L
      ((N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)).comap
        (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ⁻¹ : 𝓞 L →+* 𝓞 L)) := by
    rwa [comap_comap_inv]
  have := sigmaAdelicAct_mem_levelOne σ⁻¹ _ h'
  rwa [sigmaAdelicAct_apply_inv] at this

theorem sigmaAdelicAct_mem_levelOne_inf_iff (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ↔
      g ∈ levelOne (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
        finiteAdelicGL2Subgroup L := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, sigmaAdelicAct_mem_levelOne_iff,
    sigmaAdelicAct_mem_finiteAdelicGL2Subgroup_iff]

omit [NumberField K] in

theorem sigmaAdelicAct_weyl (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    sigmaAdelicAct K L D σ (weyl (𝓞 L) L) = weyl (𝓞 L) L := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sigmaAdelicAct_apply]
  change (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) =
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
  fin_cases i <;> fin_cases j <;> simp

theorem sigmaAdelicAct_mem_principalLevel_iff (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ principalLevel (𝓞 L) L N ↔
      g ∈ principalLevel (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) := by
  set N' := N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) with hN'
  rw [mem_principalLevel_iff, mem_principalLevel_iff, sigmaAdelicAct_mem_levelOne_iff]
  refine and_congr Iff.rfl ?_
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    refine ⟨sigmaAdelicAct K L (Dg K L) σ⁻¹ h, ?_, ?_⟩
    · rw [← sigmaAdelicAct_mem_levelOne_iff, sigmaAdelicAct_inv_apply]
      exact hh
    · have h1 := congrArg (sigmaAdelicAct K L (Dg K L) σ⁻¹) hhx
      rw [sigmaAdelicAct_apply_inv] at h1
      rw [← h1]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, sigmaAdelicAct_weyl]
  · rintro ⟨h, hh, hhx⟩
    refine ⟨sigmaAdelicAct K L (Dg K L) σ h, (sigmaAdelicAct_mem_levelOne_iff σ N h).2 hh, ?_⟩
    rw [← hhx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, sigmaAdelicAct_weyl]

theorem sigmaAdelicAct_mem_principalLevel_inf_iff (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L (Dg K L) σ g ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ↔
      g ∈ principalLevel (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
        finiteAdelicGL2Subgroup L := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, sigmaAdelicAct_mem_principalLevel_iff,
    sigmaAdelicAct_mem_finiteAdelicGL2Subgroup_iff]

theorem glFin_sigmaAdelicAct_congr (σ : L ≃ₐ[K] L) {g g' : AdelicGL2 (𝓞 L) L}
    (h : glFin (𝓞 L) L g = glFin (𝓞 L) L g') :
    glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g) = glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g') := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext L fun w' => ?_)
  rw [glFin_apply, glFin_apply, sigmaAdelicAct_snd', sigmaAdelicAct_snd']
  have h1 := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j (σ⁻¹ • w')) h
  simp only [glFin_apply] at h1
  rw [h1]

omit [NumberField K] [NumberField L] in

theorem norm_transport_infinite (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w')
    (x : w.Completion) : ‖NumberField.InfinitePlaceTransport.transport σ h x‖ = ‖x‖ := by
  obtain ⟨x, rfl⟩ := NumberField.InfinitePlace.Completion.ofCompletion_surjective w x
  refine UniformSpace.Completion.induction_on
    (p := fun y => ‖NumberField.InfinitePlaceTransport.transport σ h
      (NumberField.InfinitePlace.Completion.ofCompletion y : w.Completion)‖
        = ‖(NumberField.InfinitePlace.Completion.ofCompletion y : w.Completion)‖) x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp ((NumberField.InfinitePlaceTransport.continuous_transport σ h).comp
      (NumberField.InfinitePlace.Completion.continuous_ofCompletion w)))
      (continuous_norm.comp (NumberField.InfinitePlace.Completion.continuous_ofCompletion w))
  · intro a
    change ‖NumberField.InfinitePlaceTransport.transport σ h (a : w.Completion)‖ = ‖(a : w.Completion)‖
    rw [NumberField.InfinitePlaceTransport.transport_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe, WithAbs.congr_apply]
    exact NumberField.InfinitePlaceTransport.apply_apply_of_smul_eq h _

omit [NumberField K] [Algebra K L] in

theorem rowIsometryInclAt₀_fst_self (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    (((rowIsometryInclAt₀ L w κ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 w =
      ((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [← glArch_apply, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]
  exact archMatrixUpdate_apply_self L w _ i j

omit [NumberField K] [Algebra K L] in

theorem rowIsometryInclAt₀_fst_of_ne (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2)
    {v : InfinitePlace L} (hvw : v ≠ w) :
    (((rowIsometryInclAt₀ L w κ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 v =
      (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  rw [← glArch_apply, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]
  exact archMatrixUpdate_apply_of_ne L w _ i j hvw

omit [NumberField K] [Algebra K L] in

theorem rowIsometryInclAt₀_snd (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    (((rowIsometryInclAt₀ L w κ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j := by
  rw [← glFin_apply, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]
  rfl

omit [NumberField K] [Algebra K L] [NumberField L] in

theorem map_one_matrix_apply {A B : Type*} [Semiring A] [Semiring B] {F : Type*} [FunLike F A B]
    [RingHomClass F A B] (e : F) (i j : Fin 2) :
    e ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

def transportRowIsometry (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) :
    rowIsometrySubgroup₀ (σ • w).Completion :=
  rowIsometrySubgroup₀Map (NumberField.InfinitePlaceTransport.transport σ (rfl : σ • w = σ • w))
    (norm_transport_infinite σ rfl) κ

omit [NumberField K] [NumberField L] in
theorem transportRowIsometry_apply (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion)
    (i j : Fin 2) :
    ((transportRowIsometry σ w κ : GL (Fin 2) (σ • w).Completion) : Matrix (Fin 2) (Fin 2) (σ • w).Completion) i j =
      NumberField.InfinitePlaceTransport.transport σ (rfl : σ • w = σ • w)
        (((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) :=
  rfl

theorem sigmaAdelicAct_rowIsometryInclAt₀ (σ : L ≃ₐ[K] L) (w : InfinitePlace L)
    (κ : rowIsometrySubgroup₀ w.Completion) :
    sigmaAdelicAct K L (Dg K L) σ (rowIsometryInclAt₀ L w κ) =
      rowIsometryInclAt₀ L (σ • w) (transportRowIsometry σ w κ) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun u' => ?_) ?_)
  ·
    by_cases hu : u' = σ • w
    · subst hu
      rw [sigmaAdelicAct_fst σ _ i j (rfl : σ • w = σ • w), rowIsometryInclAt₀_fst_self,
        rowIsometryInclAt₀_fst_self, transportRowIsometry_apply]
    · have h' : σ • (σ⁻¹ • u') = u' := smul_inv_smul σ u'
      have hne : σ⁻¹ • u' ≠ w := fun he => hu (by rw [← h', he])
      rw [sigmaAdelicAct_fst σ _ i j h', rowIsometryInclAt₀_fst_of_ne _ _ _ _ hne,
        rowIsometryInclAt₀_fst_of_ne _ _ _ _ hu]
      exact map_one_matrix_apply _ i j
  ·
    refine FiniteAdeleRing.ext L fun w' => ?_
    rw [sigmaAdelicAct_snd', rowIsometryInclAt₀_snd, rowIsometryInclAt₀_snd]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      exact map_one _
    · rw [Matrix.one_apply_ne hij]
      exact map_zero _

end Genuine

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem main (σ : L ≃ₐ[K] L) (M : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L → ℂ)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgconj : ∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      g (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) = g x)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x) :
    IsBiInvariantUnder L
        (principalLevel (𝓞 L) L
            (M.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L)
        (g ∘ sigmaAdelicAct K L (Dg K L) σ) ∧
    (∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      (g ∘ sigmaAdelicAct K L (Dg K L) σ) (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) =
        (g ∘ sigmaAdelicAct K L (Dg K L) σ) x) ∧
    (∀ x : AdelicGL2 (𝓞 L) L, (g ∘ sigmaAdelicAct K L (Dg K L) σ) x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L
            (M.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L,
        glFin (𝓞 L) L u = glFin (𝓞 L) L x) := by
  set s := sigmaAdelicAct K L (Dg K L) σ with hs
  refine ⟨?_, ?_, ?_⟩
  ·
    intro u hu x
    have hu' : s u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L :=
      (sigmaAdelicAct_mem_principalLevel_inf_iff σ M u).2 hu
    refine ⟨?_, ?_⟩
    · show g (s (u * x)) = g (s x)
      rw [map_mul]
      exact (hgU (s u) hu' (s x)).1
    · show g (s (x * u)) = g (s x)
      rw [map_mul]
      exact (hgU (s u) hu' (s x)).2
  ·
    intro w κ x
    show g (s (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹)) = g (s x)
    rw [map_mul, map_mul, map_inv, hs, sigmaAdelicAct_rowIsometryInclAt₀]
    exact hgconj (σ • w) (transportRowIsometry σ w κ) _
  ·
    intro x hx
    obtain ⟨u, hu, hux⟩ := hgsupp (s x) hx
    refine ⟨sigmaAdelicAct K L (Dg K L) σ⁻¹ u, ?_, ?_⟩
    · rw [← sigmaAdelicAct_mem_principalLevel_inf_iff σ M, sigmaAdelicAct_inv_apply]
      exact hu
    · have h1 := glFin_sigmaAdelicAct_congr σ⁻¹ hux
      rw [hs, sigmaAdelicAct_apply_inv] at h1
      exact h1

end Main

end R4SigmaKernel

end

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
open AutomorphicForm

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (M : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L → ℂ)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgconj : ∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      g (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) = g x)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x) :
    IsBiInvariantUnder L
        (principalLevel (𝓞 L) L
            (M.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L)
        (g ∘ sigmaAdelicAct K L D σ) ∧
    (∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      (g ∘ sigmaAdelicAct K L D σ) (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) =
        (g ∘ sigmaAdelicAct K L D σ) x) ∧
    (∀ x : AdelicGL2 (𝓞 L) L, (g ∘ sigmaAdelicAct K L D σ) x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L
            (M.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L,
        glFin (𝓞 L) L u = glFin (𝓞 L) L x) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = R4SigmaKernel.Dg K L := Subsingleton.elim _ _
  exact R4SigmaKernel.main σ M g hgU hgconj hgsupp

end S_AutomorphicForm_isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct
end P2MW
export P2MW.S_AutomorphicForm_isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct (solution)
