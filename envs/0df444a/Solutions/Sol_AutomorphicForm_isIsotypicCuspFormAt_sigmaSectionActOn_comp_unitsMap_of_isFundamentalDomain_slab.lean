-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/08f2469a-ac56-580e-99a4-b722ef88d3fd

import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_AutomorphicForm_measurePreserving_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped NumberField.PlaceTransport Pointwise ENNReal NNReal

noncomputable section

namespace R4TwistSigmaGen

section Genuine

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Dg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L :=
  M4aHerbrand.GenuineDescent.genuineDescentDatum K L

theorem sigmaAdelicAct_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem sigmaAdelicAct_inv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) : sigmaAdelicAct K L D σ (sigmaAdelicAct K L D σ⁻¹ g) = g := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, mul_inv_cancel, sigmaAdelicAct_one]; rfl

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

theorem transport_one_matrix_apply (σ : L ≃ₐ[K] L) {u u' : InfinitePlace L} (h : σ • u = u') (i j : Fin 2) :
    NumberField.InfinitePlaceTransport.transport σ h ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j u) =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j u' := by
  rw [Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

omit [NumberField K] in

theorem heckeGenAt_mem_finiteAdelicGL2Subgroup (v : HeightOneSpectrum (𝓞 L)) (t : (v.adicCompletion L)ˣ) :
    heckeGenAt (𝓞 L) L v t ∈ finiteAdelicGL2Subgroup L := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one, glArch_apply, heckeGenAt_fst]

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

omit [NumberField K] in

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

omit [NumberField K] in
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

theorem sigmaAdelicAct_heckeGenAt (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w')
    (t : (w.adicCompletion L)ˣ) :
    sigmaAdelicAct K L (Dg K L) σ (heckeGenAt (𝓞 L) L w t) =
      heckeGenAt (𝓞 L) L w' (NumberField.PlaceTransport.transportUnits σ h t) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  ·
    have h1 := (mem_finiteAdelicGL2Subgroup_iff L _).1
      (sigmaAdelicAct_mem_finiteAdelicGL2Subgroup σ (heckeGenAt_mem_finiteAdelicGL2Subgroup w t))
    have h2 := (mem_finiteAdelicGL2Subgroup_iff L _).1
      (heckeGenAt_mem_finiteAdelicGL2Subgroup w' (NumberField.PlaceTransport.transportUnits σ h t))
    have e := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing L) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j)
      (h1.trans h2.symm)
    exact e
  · refine FiniteAdeleRing.ext L fun v => ?_
    by_cases hvw : v = w'
    · subst hvw
      rw [sigmaAdelicAct_snd σ _ i j h, heckeGenAt_snd_apply_self, heckeGenAt_snd_apply_self]
      fin_cases i <;> fin_cases j <;> simp
    · have hv : σ • (σ⁻¹ • v) = v := smul_inv_smul σ v
      have hne : σ⁻¹ • v ≠ w := by
        intro he; apply hvw; rw [← hv, he, h]
      rw [sigmaAdelicAct_snd σ _ i j hv, heckeGenAt_snd_apply_of_ne _ hne, heckeGenAt_snd_apply_of_ne _ hvw]
      fin_cases i <;> fin_cases j <;> simp

end Genuine

section Coset

open HeckeIntegralSeam

variable {G : Type*} [Group G]

theorem doubleCoset_eq_of_inv_mul_mem {U : Subgroup G} {g₁ g₂ : G} (h : g₂⁻¹ * g₁ ∈ U) :
    HeckePair.doubleCoset U g₁ = HeckePair.doubleCoset U g₂ := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff, HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, g₂⁻¹ * g₁ * v, mul_mem h hv, by group⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, (g₂⁻¹ * g₁)⁻¹ * v, mul_mem (inv_mem h) hv, by group⟩

theorem isHeckeCosetSystem_comp {U U' : Subgroup G} {g g' : G} {ι : Type*} {reps : ι → G}
    (θ : G ≃* G) (hU : ∀ x, θ x ∈ U' ↔ x ∈ U)
    (hg : HeckePair.doubleCoset U' (θ g) = HeckePair.doubleCoset U' g')
    (h : IsHeckeCosetSystem U g reps) : IsHeckeCosetSystem U' g' (θ ∘ reps) := by
  have hθ : ∀ x, x ∈ HeckePair.doubleCoset U g → θ x ∈ HeckePair.doubleCoset U' g' := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.1 hx
    rw [← hg, HeckePair.mem_doubleCoset_iff]
    exact ⟨θ u, (hU u).2 hu, θ v, (hU v).2 hv, by rw [map_mul, map_mul]⟩
  have hθ' : ∀ x, x ∈ HeckePair.doubleCoset U' g' → θ.symm x ∈ HeckePair.doubleCoset U g := by
    intro x hx
    rw [← hg, HeckePair.mem_doubleCoset_iff] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    rw [HeckePair.mem_doubleCoset_iff]
    refine ⟨θ.symm u, (hU _).1 (by rwa [MulEquiv.apply_symm_apply]), θ.symm v,
      (hU _).1 (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
  refine ⟨fun i => hθ _ (h.mem_doubleCoset i), fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers (θ.symm x) (hθ' x hx)
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have := (hU _).2 hi
    rwa [map_mul, map_inv, MulEquiv.apply_symm_apply] at this
  · apply h.mk_injective
    have hij' : (QuotientGroup.mk (θ (reps i)) : G ⧸ U') = QuotientGroup.mk (θ (reps j)) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    rw [← map_inv, ← map_mul] at hij'
    exact (hU _).1 hij'

theorem heckeCosetSum_comp {L : Type} [Field L] [NumberField L] {n : ℕ}
    (reps : Fin n → AdelicGL2 (𝓞 L) L) (θ : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    SmoothCusp.heckeCosetSum L (θ ∘ reps) φ g = ∑ i, φ (g * θ (reps i)) := rfl

end Coset

section Algebraic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (τ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D τ (centralScalar (𝓞 L) L z) =
      centralScalar (𝓞 L) L
        (Units.map ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) :=
  map_scalar (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom z

theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum.under (𝓞 K) (σ • w) = HeightOneSpectrum.under (𝓞 K) w := by
  refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 L) a = algebraMap (𝓞 K) (𝓞 L) a := by
    refine RingOfIntegers.ext ?_
    show σ⁻¹ (algebraMap K L (a : K)) = algebraMap K L (a : K)
    exact (σ⁻¹).commutes _
  rw [this]

def thetaInv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdelicGL2 (𝓞 L) L ≃* AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L D σ⁻¹
  invFun := sigmaAdelicAct K L D σ
  left_inv := sigmaAdelicAct_inv_apply D σ
  right_inv := sigmaAdelicAct_apply_inv D σ
  map_mul' := map_mul _

theorem thetaInv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) : thetaInv D σ g = sigmaAdelicAct K L D σ⁻¹ g := rfl

theorem isHeckeCosetSystem_reindex {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    {reps : ι → G} (e : κ ≃ ι) (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by rw [Function.comp_apply, Equiv.apply_symm_apply]; exact hi⟩
  · exact e.injective (h.mk_injective hkk')

theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ) rfl).toEquiv).symm

theorem heckeGen_inv_mul_sigmaAdelicAct_inv_heckeGen_mem (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L))
    (M : Ideal (𝓞 L)) :
    (heckeGen (𝓞 L) L w)⁻¹ * sigmaAdelicAct K L (Dg K L) σ⁻¹ (heckeGen (𝓞 L) L (σ • w)) ∈
      levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L := by
  have h : σ⁻¹ • (σ • w) = w := inv_smul_smul σ w
  have hgen : sigmaAdelicAct K L (Dg K L) σ⁻¹ (heckeGen (𝓞 L) L (σ • w)) =
      heckeGenAt (𝓞 L) L w (NumberField.PlaceTransport.transportUnits σ⁻¹ h (uniformizerUnit L (σ • w))) :=
    sigmaAdelicAct_heckeGenAt σ⁻¹ h _
  rw [hgen]
  refine Subgroup.mem_inf.2 ⟨heckeGen_inv_mul_heckeGenAt_mem_levelOne _ ?_ M, ?_⟩
  · show Valued.v (NumberField.PlaceTransport.transport σ⁻¹ h (uniformizerUnit L (σ • w) : (σ • w).adicCompletion L)) = _
    rw [NumberField.PlaceTransport.valued_transport, valued_uniformizerUnit]
  · exact mul_mem (inv_mem (heckeGenAt_mem_finiteAdelicGL2Subgroup w _))
      (heckeGenAt_mem_finiteAdelicGL2Subgroup w _)

theorem isHeckeCosetEigenfunctionAt_twist (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (u : AdelicGL2 (𝓞 L) L → ℂ) (c : ℂ)
    (hu : SmoothCusp.IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L (σ • w)) (σ • w) u c) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L
      (levelOne (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
        finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w (sigmaSectionActOn K L (Dg K L) σ u) c := by
  classical
  obtain ⟨reps, hsys, hsum⟩ := hu
  set N' := N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) with hN'

  let e : Fin (Ideal.absNorm w.asIdeal + 1) ≃ Fin (Ideal.absNorm (σ • w).asIdeal + 1) :=
    finCongr (by rw [absNorm_smul])

  have hU : ∀ x, thetaInv (Dg K L) σ x ∈ levelOne (𝓞 L) L N' ⊓ finiteAdelicGL2Subgroup L ↔
      x ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
    intro x
    rw [thetaInv_apply, ← sigmaAdelicAct_mem_levelOne_inf_iff σ N, sigmaAdelicAct_inv_apply]
  have hg : HeckePair.doubleCoset (levelOne (𝓞 L) L N' ⊓ finiteAdelicGL2Subgroup L)
      (thetaInv (Dg K L) σ (heckeGen (𝓞 L) L (σ • w))) =
        HeckePair.doubleCoset (levelOne (𝓞 L) L N' ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) :=
    doubleCoset_eq_of_inv_mul_mem (heckeGen_inv_mul_sigmaAdelicAct_inv_heckeGen_mem σ w N')
  have hsys' := isHeckeCosetSystem_reindex e (isHeckeCosetSystem_comp (thetaInv (Dg K L) σ) hU hg hsys)
  refine ⟨(thetaInv (Dg K L) σ ∘ reps) ∘ e, hsys', fun g => ?_⟩

  have hval : ∀ i, sigmaSectionActOn K L (Dg K L) σ u (g * ((thetaInv (Dg K L) σ ∘ reps) ∘ e) i) =
      u (sigmaAdelicAct K L (Dg K L) σ g * reps (e i)) := by
    intro i
    show u (sigmaAdelicAct K L (Dg K L) σ (g * sigmaAdelicAct K L (Dg K L) σ⁻¹ (reps (e i)))) = _
    rw [map_mul, sigmaAdelicAct_inv_apply]
  unfold SmoothCusp.heckeCosetSum
  simp_rw [hval]
  rw [Fintype.sum_equiv e (fun i => u (sigmaAdelicAct K L (Dg K L) σ g * reps (e i)))
    (fun j => u (sigmaAdelicAct K L (Dg K L) σ g * reps j)) (fun _ => rfl)]
  exact hsum (sigmaAdelicAct K L (Dg K L) σ g)

theorem isKfSmooth_twist (σ : L ≃ₐ[K] L) (u : AdelicGL2 (𝓞 L) L → ℂ) (hu : IsKfSmooth L u) :
    IsKfSmooth L (sigmaSectionActOn K L (Dg K L) σ u) := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer] at hu ⊢

  let ψ : finiteAdelicGL2Subgroup L →* finiteAdelicGL2Subgroup L :=
    { toFun := fun k => ⟨sigmaAdelicAct K L (Dg K L) σ k, sigmaAdelicAct_mem_finiteAdelicGL2Subgroup σ k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hψ : Continuous ψ :=
    Continuous.subtype_mk ((continuous_sigmaAdelicAct K L (Dg K L) σ).comp continuous_subtype_val) _
  refine Subgroup.isOpen_mono (H₁ := (MulAction.stabilizer (finiteAdelicGL2Subgroup L)
    (FLT.SmoothVectors.RightTranslationFn.mk u)).comap ψ) ?_ (hu.preimage hψ)
  intro k hk
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  rw [MulAction.mem_stabilizer_iff]
  refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
  have hx := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (sigmaAdelicAct K L (Dg K L) σ x)) hk
  simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk] at hx ⊢
  show u (sigmaAdelicAct K L (Dg K L) σ (x * k)) = u (sigmaAdelicAct K L (Dg K L) σ x)
  rw [map_mul]
  exact hx

end Algebraic

section Slab

variable {L : Type} [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) L) := by
  haveI := countable_numberField (L := L)
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl2 (L := L)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L))

def slab (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

scoped instance smulInvariantMeasure_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨g, γ₀, rfl⟩ := γ
  have hpre : (fun x : AdelicGL2 (𝓞 L) L =>
      (⟨globalPoints (𝓞 L) L γ₀, γ₀, rfl⟩ : (globalPoints (𝓞 L) L).range) • x) ⁻¹' s =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s := rfl
  rw [hpre, Measure.restrict_apply ((measurable_const_mul _) hs), Measure.restrict_apply hs]
  have hset : (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s ∩ slab L α β =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem memLp_two_of_isFundamentalDomain {α β : ℝ} {s t : Set (AdelicGL2 (𝓞 L) L)}
    (hs : IsFundamentalDomain (globalPoints (𝓞 L) L).range s ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (ht : IsFundamentalDomain (globalPoints (𝓞 L) L).range t ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : ∀ (γ : GL (Fin 2) L) (x), f (globalPoints (𝓞 L) L γ * x) = f x)
    (h : MemLp f 2 (((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)).restrict s)) :
    MemLp f 2 (((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)).restrict t) := by
  have hinv : ∀ (γ : (globalPoints (𝓞 L) L).range) (x : AdelicGL2 (𝓞 L) L), f (γ • x) = f x := by
    rintro ⟨g, γ₀, rfl⟩ x
    exact hf γ₀ x
  refine ⟨(hs.aestronglyMeasurable_on_iff ht hinv).1 h.1, ?_⟩
  have h2 := h.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h2 ⊢
  have key := hs.setLIntegral_eq ht (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal) fun γ x => by
    show ‖f (γ • x)‖ₑ ^ (2 : ℝ≥0∞).toReal = ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal
    rw [hinv]
  rw [← key]
  exact h2

variable {K : Type} [Field K] [NumberField K] [Algebra K L]

def sigmaHomeo (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdelicGL2 (𝓞 L) L ≃ₜ AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L D σ
  invFun := sigmaAdelicAct K L D σ⁻¹
  left_inv := sigmaAdelicAct_apply_inv D σ
  right_inv := sigmaAdelicAct_inv_apply D σ
  continuous_toFun := continuous_sigmaAdelicAct K L D σ
  continuous_invFun := continuous_sigmaAdelicAct K L D σ⁻¹

theorem sigmaAdelicAct_mem_slab_iff (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {α β : ℝ} (x : AdelicGL2 (𝓞 L) L) : sigmaAdelicAct K L D σ x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ x]

theorem preimage_slab (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (α β : ℝ) :
    sigmaAdelicAct K L D σ ⁻¹' slab L α β = slab L α β :=
  Set.ext fun x => sigmaAdelicAct_mem_slab_iff D σ x

theorem measurePreserving_slab (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (α β : ℝ) :
    MeasurePreserving (sigmaAdelicAct K L D σ)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  have h := (AutomorphicForm.measurePreserving_sigmaAdelicAct K L D σ).restrict_preimage (measurableSet_slab α β)
  rwa [preimage_slab] at h

theorem isFundamentalDomain_image (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))) :
    IsFundamentalDomain (globalPoints (𝓞 L) L).range (sigmaAdelicAct K L D σ '' Φ)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by

  have hmem : ∀ (τ : L ≃ₐ[K] L) (γ : AdelicGL2 (𝓞 L) L), γ ∈ (globalPoints (𝓞 L) L).range →
      sigmaAdelicAct K L D τ γ ∈ (globalPoints (𝓞 L) L).range := by
    rintro τ _ ⟨γ₀, rfl⟩
    exact ⟨Matrix.GeneralLinearGroup.map (τ : L →+* L) γ₀, (sigmaAdelicAct_globalPoints K L D τ γ₀).symm⟩
  let e : (globalPoints (𝓞 L) L).range ≃ (globalPoints (𝓞 L) L).range :=
    { toFun := fun γ => ⟨sigmaAdelicAct K L D σ⁻¹ γ, hmem σ⁻¹ γ γ.2⟩
      invFun := fun γ => ⟨sigmaAdelicAct K L D σ γ, hmem σ γ γ.2⟩
      left_inv := fun γ => Subtype.ext (sigmaAdelicAct_inv_apply D σ γ)
      right_inv := fun γ => Subtype.ext (sigmaAdelicAct_apply_inv D σ γ) }
  refine hΦ.image_of_equiv (sigmaHomeo D σ).toEquiv
    (measurePreserving_slab D σ⁻¹ α β).quasiMeasurePreserving e fun γ x => ?_
  show sigmaAdelicAct K L D σ (sigmaAdelicAct K L D σ⁻¹ (γ : AdelicGL2 (𝓞 L) L) * x) =
    (γ : AdelicGL2 (𝓞 L) L) * sigmaAdelicAct K L D σ x
  rw [map_mul, sigmaAdelicAct_inv_apply]

theorem memLp_twist (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {α β : ℝ} {ΦL : Set (AdelicGL2 (𝓞 L) L)} (hΦs : ΦL ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (u : AdelicGL2 (𝓞 L) L → ℂ) (hul : ∀ (γ : GL (Fin 2) L) (x), u (globalPoints (𝓞 L) L γ * x) = u x)
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL)) :
    MemLp (sigmaSectionActOn K L D σ u) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set T := (sigmaHomeo D σ).toMeasurableEquiv with hT
  have hTco : (T : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) = sigmaAdelicAct K L D σ := rfl

  have h1 : MemLp u 2 ((μ.restrict (slab L α β)).restrict ΦL) := by
    rwa [Measure.restrict_restrict_of_subset hΦs]
  have h2 : MemLp u 2 ((μ.restrict (slab L α β)).restrict (sigmaAdelicAct K L D σ '' ΦL)) :=
    memLp_two_of_isFundamentalDomain hΦ (isFundamentalDomain_image D σ hΦ) u hul h1
  have hsub : sigmaAdelicAct K L D σ '' ΦL ⊆ slab L α β := by
    rintro _ ⟨x, hx, rfl⟩
    exact (sigmaAdelicAct_mem_slab_iff D σ x).2 (hΦs hx)
  rw [Measure.restrict_restrict_of_subset hsub] at h2

  have hmap : μ.restrict (sigmaAdelicAct K L D σ '' ΦL) = Measure.map T (μ.restrict ΦL) := by
    have hpre : (T : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) ⁻¹' (sigmaAdelicAct K L D σ '' ΦL) = ΦL := by
      rw [hTco]
      exact (sigmaHomeo D σ).injective.preimage_image ΦL
    have hme : Measure.map T μ = μ := (AutomorphicForm.measurePreserving_sigmaAdelicAct K L D σ).map_eq
    conv_lhs => rw [← hme]
    rw [T.restrict_map, hpre]
  rw [hmap, T.memLp_map_measure_iff] at h2
  exact h2

end Slab

section Additive

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem act_inv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act τ : RingAut (AdeleRing (𝓞 L) L)) x) = x := by
  calc (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act τ : RingAut (AdeleRing (𝓞 L) L)) x)
        = (D.act τ⁻¹ * D.act τ : RingAut (AdeleRing (𝓞 L) L)) x := rfl
    _ = x := by rw [← map_mul, inv_mul_cancel, map_one]; rfl

theorem act_apply_inv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    (D.act τ : RingAut (AdeleRing (𝓞 L) L)) ((D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) x) = x := by
  have h := act_inv_apply D τ⁻¹ x
  rwa [inv_inv] at h

def actHomeo (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ AdeleRing (𝓞 L) L where
  toFun := (D.act τ : RingAut (AdeleRing (𝓞 L) L))
  invFun := (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L))
  left_inv := act_inv_apply D τ
  right_inv := act_apply_inv D τ
  continuous_toFun := D.continuous_act τ
  continuous_invFun := D.continuous_act τ⁻¹

theorem coe_actHomeo (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    (actHomeo D τ : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act τ : RingAut (AdeleRing (𝓞 L) L)) := rfl

theorem regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  dsimp only [adelicAddHaar, Measure.addHaar]
  infer_instance

attribute [local instance] regular_adelicAddHaar

theorem map_act_eq_smul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    ∃ c : ℝ≥0, Measure.map (D.act τ : RingAut (AdeleRing (𝓞 L) L)) (adelicAddHaar (𝓞 L) L) =
      c • adelicAddHaar (𝓞 L) L := by
  set ν := adelicAddHaar (𝓞 L) L with hν
  let e : AdeleRing (𝓞 L) L ≃+ AdeleRing (𝓞 L) L := (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toAddEquiv
  have he : Continuous e := D.continuous_act τ
  have hsymm : (e.symm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) =
      (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
    funext x
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    exact (act_apply_inv D τ x).symm
  have he' : Continuous e.symm := by
    rw [hsymm]; exact D.continuous_act τ⁻¹
  haveI : (Measure.map e ν).IsAddHaarMeasure := e.isAddHaarMeasure_map ν he he'
  haveI : (Measure.map e ν).Regular := Measure.Regular.map (actHomeo D τ)
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.map e ν) ν⟩

theorem measurePreserving_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    MeasurePreserving (D.act τ : RingAut (AdeleRing (𝓞 L) L)) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  set ν := adelicAddHaar (𝓞 L) L with hν
  have hmeas : ∀ ρ : L ≃ₐ[K] L, Measurable (D.act ρ : RingAut (AdeleRing (𝓞 L) L)) :=
    fun ρ => (D.continuous_act ρ).measurable
  obtain ⟨c, h1'⟩ := map_act_eq_smul D τ
  have h1 : Measure.map (D.act τ : RingAut (AdeleRing (𝓞 L) L)) ν = (c : ℝ≥0∞) • ν := h1'

  have hk : ∀ k : ℕ, Measure.map (D.act (τ ^ k) : RingAut (AdeleRing (𝓞 L) L)) ν = (c : ℝ≥0∞) ^ k • ν := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, one_smul, map_one]
      exact Measure.map_id
    | succ k ih =>
      have hcomp : ((D.act (τ ^ (k + 1)) : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) =
          (D.act τ : RingAut (AdeleRing (𝓞 L) L)) ∘ (D.act (τ ^ k) : RingAut (AdeleRing (𝓞 L) L)) := by
        rw [pow_succ', map_mul]; rfl
      rw [hcomp, ← Measure.map_map (hmeas τ) (hmeas _), ih, Measure.map_smul, h1, smul_smul,
        pow_succ]

  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨n, hn, hτn⟩ : ∃ n : ℕ, 0 < n ∧ τ ^ n = 1 := ⟨orderOf τ, orderOf_pos τ, pow_orderOf_eq_one τ⟩
  have hνn : ν = (c : ℝ≥0∞) ^ n • ν := by
    have h := hk n
    rw [hτn, map_one] at h
    rw [← h]
    exact Measure.map_id.symm

  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : ν s ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨0, mem_interior_iff_mem_nhds.mpr hs_mem⟩).ne'
  have hstop : ν s ≠ ∞ := hs_compact.measure_lt_top.ne
  have hcn : c ^ n = 1 := by
    have h := congrArg (fun m : Measure (AdeleRing (𝓞 L) L) => m s) hνn
    simp only [Measure.smul_apply, smul_eq_mul] at h
    have h' : ((c : ℝ≥0∞) ^ n) = 1 := ((ENNReal.mul_left_inj hs0 hstop).1 ((one_mul _).trans h)).symm
    exact_mod_cast h'
  have hc1 : c = 1 := (pow_left_inj₀ (zero_le (a := c)) zero_le_one hn.ne').1 (by rwa [one_pow])
  refine ⟨hmeas τ, ?_⟩
  rw [h1, hc1, ENNReal.coe_one, one_smul]

theorem sigmaAdelicAct_unipotentGL2 (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (q : AdeleRing (𝓞 L) L) :
    sigmaAdelicAct K L D σ (unipotentGL2 q) = unipotentGL2 ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) q) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sigmaAdelicAct_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] in

theorem unipotentGL2_algebraMap (k : L) :
    unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) = globalPoints (𝓞 L) L (unipotentGL2 k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (!![(1 : AdeleRing (𝓞 L) L), algebraMap L (AdeleRing (𝓞 L) L) k; 0, 1]) i j =
    algebraMap L (AdeleRing (𝓞 L) L) ((!![(1 : L), k; 0, 1]) i j)
  fin_cases i <;> fin_cases j <;> simp

scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 L) L) := by
  haveI := countable_numberField (L := L)
  refine Function.Surjective.countable (f := fun k : L => (⟨algebraMap L (AdeleRing (𝓞 L) L) k, k, rfl⟩ :
    AdeleRing.principalSubgroup (𝓞 L) L)) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

scoped instance vaddInvariantMeasure_principal :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 L) L) (AdeleRing (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  refine ⟨fun a s hs => ?_⟩
  obtain ⟨a, ha⟩ := a
  exact measure_preimage_add (adelicAddHaar (𝓞 L) L) a s

theorem isAddFundamentalDomain_image_adelicBox (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L)
      (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) '' adelicBox L)
      (adelicAddHaar (𝓞 L) L) := by
  have hmem : ∀ (τ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L), a ∈ AdeleRing.principalSubgroup (𝓞 L) L →
      (D.act τ : RingAut (AdeleRing (𝓞 L) L)) a ∈ AdeleRing.principalSubgroup (𝓞 L) L := by
    rintro τ _ ⟨k, rfl⟩
    exact ⟨τ k, (D.compat τ k).symm⟩
  let e : AdeleRing.principalSubgroup (𝓞 L) L ≃ AdeleRing.principalSubgroup (𝓞 L) L :=
    { toFun := fun a => ⟨(D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) a, hmem σ⁻¹ a a.2⟩
      invFun := fun a => ⟨(D.act σ : RingAut (AdeleRing (𝓞 L) L)) a, hmem σ a a.2⟩
      left_inv := fun a => Subtype.ext (act_apply_inv D σ a)
      right_inv := fun a => Subtype.ext (act_inv_apply D σ a) }
  refine (isAddFundamentalDomain_adelicBox_adelicAddHaar L).image_of_equiv (actHomeo D σ).toEquiv
    (measurePreserving_act D σ⁻¹).quasiMeasurePreserving e fun a x => ?_
  show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) (a : AdeleRing (𝓞 L) L) + x) =
    (a : AdeleRing (𝓞 L) L) + (D.act σ : RingAut (AdeleRing (𝓞 L) L)) x
  rw [map_add, act_apply_inv]

theorem constantTerm_twist (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (u : AdelicGL2 (𝓞 L) L → ℂ) (hul : ∀ (γ : GL (Fin 2) L) (x), u (globalPoints (𝓞 L) L γ * x) = u x)
    (g : AdelicGL2 (𝓞 L) L) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2
        (sigmaSectionActOn K L D σ u) g =
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2 u
        (sigmaAdelicAct K L D σ g) := by
  have hint : ∀ q, constantTermIntegrand unipotentGL2 (sigmaSectionActOn K L D σ u) g q =
      u (unipotentGL2 ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) q) * sigmaAdelicAct K L D σ g) := by
    intro q
    show u (sigmaAdelicAct K L D σ (unipotentGL2 q * g)) = _
    rw [map_mul, sigmaAdelicAct_unipotentGL2]
  have hint' : ∀ q, constantTermIntegrand unipotentGL2 u (sigmaAdelicAct K L D σ g) q =
      u (unipotentGL2 q * sigmaAdelicAct K L D σ g) := fun q => rfl
  unfold constantTerm
  simp_rw [hint, hint']
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure]
  congr 1

  have hemb : MeasurableEmbedding ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) :=
    (actHomeo D σ).toMeasurableEquiv.measurableEmbedding
  rw [← (measurePreserving_act D σ).setIntegral_image_emb hemb
    (fun q => u (unipotentGL2 q * sigmaAdelicAct K L D σ g)) (adelicBox L)]
  refine (isAddFundamentalDomain_image_adelicBox D σ).setIntegral_eq
    (isAddFundamentalDomain_adelicBox_adelicAddHaar L) fun a q => ?_
  obtain ⟨_, k, rfl⟩ := a
  show u (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k + q) * sigmaAdelicAct K L D σ g) =
    u (unipotentGL2 q * sigmaAdelicAct K L D σ g)
  rw [unipotentGL2_add, unipotentGL2_algebraMap, mul_assoc, hul]

end Additive

end R4TwistSigmaGen
p2m_reactivate "P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab.R4TwistSigmaGen"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab.R4TwistSigmaGen"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open R4TwistSigmaGen in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (Ψ : HeckeEigensystem L ℂ)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ u) :
    IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L))
      (ξL.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
        ((Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
            AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp Subgroup.topEquiv.toMonoidHom)))
      (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) SL
      ⟨Ψ.level, Ψ.level_ne_bot, fun w => Ψ.a (σ • w), fun w =>
        HeckeEigensystem.cNorm w *
          ((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
              AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)
            (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)⟩
      (sigmaSectionActOn K L D σ u) := by

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = R4TwistSigmaGen.Dg K L := Subsingleton.elim _ _

  obtain ⟨⟨hauto, hcuspu⟩, hKf⟩ := hu.smoothCusp
  have h1 : LsXiMemberAt (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ ξL ΦL u := hauto
  obtain ⟨hlsxi, hmem⟩ := (lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξL ΦL u).1 h1
  have hul : ∀ (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L γ * x) = u x :=
    hlsxi.left_invariant
  have hcen : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L),
      u (centralScalar (𝓞 L) L z * x) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u x :=
    fun z x => hlsxi.central_transform ⟨z, Subgroup.mem_top z⟩ x

  have hlsxi' : IsLsXiFunction (𝓞 L) L ⊤
      (ξL.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
        ((Units.map (((Dg K L).act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
            AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp Subgroup.topEquiv.toMonoidHom)))
      (sigmaSectionActOn K L (Dg K L) σ u) := by
    refine ⟨fun γ x => ?_, fun z x => ?_⟩
    · show u (sigmaAdelicAct K L (Dg K L) σ (globalPoints (𝓞 L) L γ * x)) = u (sigmaAdelicAct K L (Dg K L) σ x)
      rw [map_mul, show sigmaAdelicAct K L (Dg K L) σ (globalPoints (𝓞 L) L γ) =
        globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) from
          sigmaAdelicAct_globalPoints K L (Dg K L) σ γ, hul]
    · obtain ⟨z, hz⟩ := z
      show u (sigmaAdelicAct K L (Dg K L) σ (centralScalar (𝓞 L) L z * x)) =
        ((ξL ⟨Units.map (((Dg K L).act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
            AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          u (sigmaAdelicAct K L (Dg K L) σ x)
      rw [map_mul, sigmaAdelicAct_centralScalar, hcen]

  have hmem' : MemLp (sigmaSectionActOn K L (Dg K L) σ u) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) :=
    memLp_twist (Dg K L) σ hΦs hΦ u hul hmem

  have hcusp' : IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2
      (sigmaSectionActOn K L (Dg K L) σ u) :=
    fun g => (constantTerm_twist (Dg K L) σ u hul g).trans (hcuspu _)

  have hKf' : IsKfSmooth L (sigmaSectionActOn K L (Dg K L) σ u) := isKfSmooth_twist σ u hKf
  refine ⟨⟨⟨(lsXiMemberAt_iff (𝓞 L) L _ ⊤ _ ΦL _).2 ⟨hlsxi', hmem'⟩, hcusp'⟩, hKf'⟩,
    hu.continuous.comp (continuous_sigmaAdelicAct K L (Dg K L) σ), fun g k hk => ?_, fun w hw => ?_,
    fun w hw g => ?_⟩
  ·
    show u (sigmaAdelicAct K L (Dg K L) σ (g * k)) = u (sigmaAdelicAct K L (Dg K L) σ g)
    rw [map_mul]
    exact hu.level_invariant _ _ ((sigmaAdelicAct_mem_levelOne_inf_iff σ N k).2 hk)
  ·
    have hσw : σ • w ∉ SL := fun h => hw ((hSL (σ • w) w (under_smul σ w)).1 h)
    exact isHeckeCosetEigenfunctionAt_twist σ N w u (Ψ.a (σ • w)) (hu.hecke_eigen (σ • w) hσw)
  ·
    show u (sigmaAdelicAct K L (Dg K L) σ
        (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g)) =
      (HeckeEigensystem.cNorm w)⁻¹ * (HeckeEigensystem.cNorm w *
        ((ξL ⟨Units.map (((Dg K L).act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
            AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)
          (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) *
        u (sigmaAdelicAct K L (Dg K L) σ g)
    rw [map_mul, sigmaAdelicAct_centralScalar, hcen, ← mul_assoc,
      inv_mul_cancel₀ (HeckeEigensystem.cNorm_ne_zero w), one_mul]

end S_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab (solution)
