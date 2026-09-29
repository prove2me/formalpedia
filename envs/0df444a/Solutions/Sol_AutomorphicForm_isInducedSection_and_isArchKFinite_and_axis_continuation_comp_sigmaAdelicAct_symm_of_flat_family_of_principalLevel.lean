-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0d879664-4315-564c-8cc2-f3d4419751b5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped NumberField.PlaceTransport Pointwise ENNReal NNReal ComplexConjugate

noncomputable section

namespace R4SecTransEngine

open NumberField.TateGlobal

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

end Genuine

section Act

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

theorem sigmaAdelicAct_unipotentGL2_algebraMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξ : L) :
    sigmaAdelicAct K L D σ (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ)) =
      unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) (σ ξ)) := by
  rw [sigmaAdelicAct_unipotentGL2, D.compat]

end Act

section NewLemmas

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem sigmaAdelicAct_adelicWeyl (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    sigmaAdelicAct K L D σ (adelicWeyl (𝓞 L) L) = adelicWeyl (𝓞 L) L := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sigmaAdelicAct_apply]
  change (D.act σ : RingAut (AdeleRing (𝓞 L) L))
      (algebraMap L (AdeleRing (𝓞 L) L) (((gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j)) =
    algebraMap L (AdeleRing (𝓞 L) L) (((gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j)
  rw [D.compat, gl2Weyl_val]
  congr 1
  fin_cases i <;> fin_cases j <;> simp

theorem sigmaAdelicAct_weyl (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    sigmaAdelicAct K L D σ (weyl (𝓞 L) L) = weyl (𝓞 L) L := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sigmaAdelicAct_apply]
  change (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((!![(0 : AdeleRing (𝓞 L) L), 1; 1, 0]) i j) =
    (!![(0 : AdeleRing (𝓞 L) L), 1; 1, 0]) i j
  fin_cases i <;> fin_cases j <;> simp

theorem sigmaAdelicAct_mem_adelicBorel (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {b : AdelicGL2 (𝓞 L) L} (hb : b ∈ adelicBorel (𝓞 L) L) :
    sigmaAdelicAct K L D σ b ∈ adelicBorel (𝓞 L) L := by
  rw [mem_borelSubgroup_iff] at hb ⊢
  rw [sigmaAdelicAct_apply, hb, map_zero]

theorem unitsAct_eq_map (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ z = Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z :=
  Units.ext rfl

theorem borelDiag_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {b : AdelicGL2 (𝓞 L) L} (hb : b ∈ adelicBorel (𝓞 L) L) :
    borelDiagFst (⟨sigmaAdelicAct K L D σ b, sigmaAdelicAct_mem_adelicBorel D σ hb⟩ : ↥(adelicBorel (𝓞 L) L)) =
        D.unitsAct σ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) ∧
      borelDiagSnd (⟨sigmaAdelicAct K L D σ b, sigmaAdelicAct_mem_adelicBorel D σ hb⟩ : ↥(adelicBorel (𝓞 L) L)) =
        D.unitsAct σ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) := by
  constructor
  · apply Units.ext
    rw [borelDiagFst_apply_val, unitsAct_eq_map, Units.coe_map, borelDiagFst_apply_val]
    exact sigmaAdelicAct_apply D σ b 0 0
  · apply Units.ext
    rw [borelDiagSnd_apply_val, unitsAct_eq_map, Units.coe_map, borelDiagSnd_apply_val]
    exact sigmaAdelicAct_apply D σ b 1 1

end NewLemmas

section Modulus
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne
  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b
  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl
  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    first | (funext a; exact θ.apply_symm_apply a) | exact θ.apply_symm_apply _
  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1
  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

theorem unitsAct_eq_map' (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ z = Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z :=
  Units.ext rfl

theorem ideleNorm_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L (D.unitsAct σ z) = ideleNorm L z := by
  rw [unitsAct_eq_map']; exact ideleNorm_unitsMap_act K L D σ z

theorem cpowChar_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ))
    (s : ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    cpowChar αL hα s (D.unitsAct g z) =
    cpowChar αL hα s z := by
  apply Units.ext
  rw [cpowChar_apply_val, cpowChar_apply_val]
  have h : ((αL (D.unitsAct g z) : ℝˣ) : ℝ) = ((αL z : ℝˣ) : ℝ) := ideleNorm_unitsAct K L D g z
  rw [h]

theorem unitsAct_symm_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ.symm (D.unitsAct σ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, show σ.symm * σ = 1 from mul_eq_one_iff_eq_inv.mpr rfl, map_one,
    MulAut.one_apply]

theorem unitsAct_apply_symm (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) : D.unitsAct σ (D.unitsAct σ.symm z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, show σ * σ.symm = 1 from mul_eq_one_iff_eq_inv.mpr rfl, map_one,
    MulAut.one_apply]
end Modulus

section Arch

open AutomorphicForm.WindowedSiegel

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in

theorem norm_transport_infinite (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w')
    (x : w.Completion) : ‖NumberField.InfinitePlaceTransport.transport σ h x‖ = ‖x‖ := by
  refine NumberField.InfinitePlace.Completion.induction_on _
    (p := fun x : w.Completion => ‖NumberField.InfinitePlaceTransport.transport σ h x‖ = ‖x‖) x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (NumberField.InfinitePlaceTransport.continuous_transport σ h))
      continuous_norm
  · intro a
    rw [NumberField.InfinitePlaceTransport.transport_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe]
    exact NumberField.InfinitePlaceTransport.apply_apply_of_smul_eq h _

theorem archComponent_sigmaAdelicAct (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L)
    {u u' : InfinitePlace L} (h : σ • u = u') :
    archComponent L u' (glArch (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g)) =
      Matrix.GeneralLinearGroup.map (NumberField.InfinitePlaceTransport.transport σ h).toRingHom
        (archComponent L u (glArch (𝓞 L) L g)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, glArch_apply, sigmaAdelicAct_apply]
  change _ = NumberField.InfinitePlaceTransport.transport σ h
    ((archComponent L u (glArch (𝓞 L) L g) : Matrix (Fin 2) (Fin 2) u.Completion) i j)
  rw [archComponent_apply, glArch_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ h

omit [NumberField K] [Algebra K L] in

theorem isRowIsometry_map {u u' : InfinitePlace L} (φ : u.Completion ≃+* u'.Completion)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) {k : GL (Fin 2) u.Completion} (hk : IsRowIsometry k) :
    IsRowIsometry (Matrix.GeneralLinearGroup.map φ.toRingHom k) := by
  obtain ⟨hdet, hrow⟩ := hk
  have hent : ∀ i j : Fin 2, ((Matrix.GeneralLinearGroup.map φ.toRingHom k : GL (Fin 2) u'.Completion) :
      Matrix (Fin 2) (Fin 2) u'.Completion) i j = φ ((k : Matrix (Fin 2) (Fin 2) u.Completion) i j) :=
    fun i j => Matrix.GeneralLinearGroup.map_apply _ i j k
  constructor
  · have hM : ((Matrix.GeneralLinearGroup.map φ.toRingHom k : GL (Fin 2) u'.Completion) :
        Matrix (Fin 2) (Fin 2) u'.Completion) = (k : Matrix (Fin 2) (Fin 2) u.Completion).map φ := by
      ext i j; exact hent i j
    rw [hM]
    have hd : ((k : Matrix (Fin 2) (Fin 2) u.Completion).map φ).det =
        φ (k : Matrix (Fin 2) (Fin 2) u.Completion).det := by
      have := (RingHom.map_det (φ : u.Completion →+* u'.Completion) (k : Matrix (Fin 2) (Fin 2) u.Completion)).symm
      simpa using this
    rw [hd, hφ, hdet]
  · intro x y
    obtain ⟨x₀, rfl⟩ := φ.surjective x
    obtain ⟨y₀, rfl⟩ := φ.surjective y
    have key := hrow x₀ y₀
    rw [hent, hent, hent, hent]
    have e1 : φ x₀ * φ ((k : Matrix (Fin 2) (Fin 2) u.Completion) 0 0) +
        φ y₀ * φ ((k : Matrix (Fin 2) (Fin 2) u.Completion) 1 0) =
        φ (x₀ * (k : Matrix (Fin 2) (Fin 2) u.Completion) 0 0 + y₀ * (k : Matrix (Fin 2) (Fin 2) u.Completion) 1 0) := by
      rw [map_add, map_mul, map_mul]
    have e2 : φ x₀ * φ ((k : Matrix (Fin 2) (Fin 2) u.Completion) 0 1) +
        φ y₀ * φ ((k : Matrix (Fin 2) (Fin 2) u.Completion) 1 1) =
        φ (x₀ * (k : Matrix (Fin 2) (Fin 2) u.Completion) 0 1 + y₀ * (k : Matrix (Fin 2) (Fin 2) u.Completion) 1 1) := by
      rw [map_add, map_mul, map_mul]
    rw [e1, e2, hφ, hφ, hφ, hφ]
    exact key

theorem sigmaAdelicAct_mem_adelicMaximalCompact (σ : L ≃ₐ[K] L) {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ adelicMaximalCompact L) : sigmaAdelicAct K L (Dg K L) σ k ∈ adelicMaximalCompact L := by
  rw [mem_adelicMaximalCompact_iff] at hk ⊢
  refine ⟨(AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
    K L (Dg K L) σ k).2 hk.1, fun w => ?_⟩
  rw [archComponent_sigmaAdelicAct σ k (smul_inv_smul σ w)]
  exact isRowIsometry_map _ (norm_transport_infinite σ (smul_inv_smul σ w)) (hk.2 _)

theorem adelicArchGLInclAt_fst_apply {u : InfinitePlace L} (k₀ : GL (Fin 2) u.Completion) (i j : Fin 2)
    (v : InfinitePlace L) :
    (((adelicArchGLInclAt L u k₀ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 v =
      ((archComponent L v (archGLIncl L u k₀) : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  rw [archComponent_apply, ← glArch_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]

theorem adelicArchGLInclAt_snd {u : InfinitePlace L} (k₀ : GL (Fin 2) u.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt L u k₀ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j := by
  rw [← glFin_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]
  rfl

theorem sigmaAdelicAct_adelicArchGLInclAt (σ : L ≃ₐ[K] L) (u : InfinitePlace L)
    (k₀ : GL (Fin 2) u.Completion) :
    sigmaAdelicAct K L (Dg K L) σ (adelicArchGLInclAt L u k₀) =
      adelicArchGLInclAt L (σ • u)
        (Matrix.GeneralLinearGroup.map (NumberField.InfinitePlaceTransport.transport σ (rfl : σ • u = σ • u)).toRingHom k₀) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun v => ?_) (RestrictedProduct.ext _ _ fun w => ?_))
  ·
    have hv : σ • (σ⁻¹ • v) = v := smul_inv_smul σ v
    rw [sigmaAdelicAct_fst σ _ i j hv, adelicArchGLInclAt_fst_apply, adelicArchGLInclAt_fst_apply]
    by_cases hvu : v = σ • u
    · subst hvu

      have key : ∀ (x : InfinitePlace L) (hx : σ • x = σ • u) (hxu : x = u),
          NumberField.InfinitePlaceTransport.transport σ hx
            (((archComponent L x (archGLIncl L u k₀) : GL (Fin 2) x.Completion) :
              Matrix (Fin 2) (Fin 2) x.Completion) i j) =
          NumberField.InfinitePlaceTransport.transport σ (rfl : σ • u = σ • u)
            ((k₀ : Matrix (Fin 2) (Fin 2) u.Completion) i j) := by
        intro x hx hxu
        subst hxu
        rw [archComponent_archGLIncl_self]
      rw [key (σ⁻¹ • (σ • u)) hv (inv_smul_smul σ u), archComponent_archGLIncl_self,
        Matrix.GeneralLinearGroup.map_apply]
      rfl
    · have hne : σ⁻¹ • v ≠ u := fun h' => hvu (by rw [← h', smul_inv_smul])
      rw [archComponent_archGLIncl_of_ne L hne, archComponent_archGLIncl_of_ne L hvu, Units.val_one, Units.val_one,
        Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact map_one _
      · exact map_zero _
  ·
    show ((((sigmaAdelicAct K L (Dg K L) σ (adelicArchGLInclAt L u k₀) : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2) w =
      ((((adelicArchGLInclAt L (σ • u)
        (Matrix.GeneralLinearGroup.map (NumberField.InfinitePlaceTransport.transport σ (rfl : σ • u = σ • u)).toRingHom k₀) :
          AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2) w
    rw [sigmaAdelicAct_snd' σ _ i j w]
    have h1 : ((((adelicArchGLInclAt L u k₀ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2)
        = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j := adelicArchGLInclAt_snd k₀ i j
    have h2 : ((((adelicArchGLInclAt L (σ • u)
        (Matrix.GeneralLinearGroup.map (NumberField.InfinitePlaceTransport.transport σ (rfl : σ • u = σ • u)).toRingHom k₀) :
          AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2)
        = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j := adelicArchGLInclAt_snd _ i j
    rw [h1, h2, Matrix.one_apply]
    split_ifs
    · rw [coe_one_apply, coe_one_apply]; exact map_one _
    · rw [coe_zero_apply, coe_zero_apply]; exact map_zero _

theorem sigmaAdelicAct_mem_archRowIsometrySubgroup (σ : L ≃ₐ[K] L) {u : InfinitePlace L}
    {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ archRowIsometrySubgroup L u) :
    sigmaAdelicAct K L (Dg K L) σ k ∈ archRowIsometrySubgroup L (σ • u) := by
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
  refine Subgroup.mem_map.2 ⟨_, isRowIsometry_map _ (norm_transport_infinite σ (rfl : σ • u = σ • u)) hk₀, ?_⟩
  exact (sigmaAdelicAct_adelicArchGLInclAt σ u k₀).symm

theorem isArchKFinite_comp (σ : L ≃ₐ[K] L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : IsArchKFinite L f) :
    IsArchKFinite L (fun g => f (sigmaAdelicAct K L (Dg K L) σ g)) := by
  classical
  intro w
  obtain ⟨S, hS⟩ := hf (σ • w)
  let P : (AdelicGL2 (𝓞 L) L → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) :=
    LinearMap.funLeft ℂ ℂ (sigmaAdelicAct K L (Dg K L) σ)
  refine ⟨S.image P, fun k hk => ?_⟩
  have hmem := hS _ (sigmaAdelicAct_mem_archRowIsometrySubgroup σ hk)
  have hP := Submodule.mem_map_of_mem (f := P) hmem
  rw [Submodule.map_span] at hP
  have heq : (fun x : AdelicGL2 (𝓞 L) L => f (sigmaAdelicAct K L (Dg K L) σ (x * k))) =
      P (fun x => f (x * sigmaAdelicAct K L (Dg K L) σ k)) := by
    funext x
    rw [LinearMap.funLeft_apply, map_mul]
  rw [heq, Finset.coe_image]
  exact hP

theorem uniformSpan_comp (σ : L ≃ₐ[K] L) (f : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => f s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
    (w : InfinitePlace L) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) =>
          f s (sigmaAdelicAct K L (Dg K L) σ (g * (k : AdelicGL2 (𝓞 L) L)))) ∈ W := by
  obtain ⟨W', hW', hmem⟩ := hf (σ • w)
  let ρ : ↥(archRowIsometrySubgroup L w) → ↥(archRowIsometrySubgroup L (σ • w)) :=
    fun k => ⟨sigmaAdelicAct K L (Dg K L) σ k, sigmaAdelicAct_mem_archRowIsometrySubgroup σ k.2⟩
  let P : (↥(archRowIsometrySubgroup L (σ • w)) → ℂ) →ₗ[ℂ] (↥(archRowIsometrySubgroup L w) → ℂ) :=
    LinearMap.funLeft ℂ ℂ ρ
  haveI := hW'
  refine ⟨W'.map P, inferInstance, fun s g => ?_⟩
  have h1 := Submodule.mem_map_of_mem (f := P) (hmem s (sigmaAdelicAct K L (Dg K L) σ g))
  have heq : (fun k : ↥(archRowIsometrySubgroup L w) =>
      f s (sigmaAdelicAct K L (Dg K L) σ (g * (k : AdelicGL2 (𝓞 L) L)))) =
      P (fun k' : ↥(archRowIsometrySubgroup L (σ • w)) =>
        f s (sigmaAdelicAct K L (Dg K L) σ g * (k' : AdelicGL2 (𝓞 L) L))) := by
    funext k
    rw [LinearMap.funLeft_apply, map_mul]
  rw [heq]
  exact h1

end Arch

section Clauses

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

set_option quotPrecheck false in
local notation "αL" => (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)

theorem isInducedSection_comp (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hα : ∀ x, 0 < ((αL x : ℝˣ) : ℝ))
    (μ ν μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hμ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, μ' z = μ (D.unitsAct σ z))
    (hν' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ν' z = ν (D.unitsAct σ z))
    (s : ℂ) (f : AdelicGL2 (𝓞 L) L → ℂ)
    (hf : IsInducedSection (𝓞 L) L (etaFst μ αL hα s) (etaSnd ν αL hα s) f) :
    IsInducedSection (𝓞 L) L (etaFst μ' αL hα s) (etaSnd ν' αL hα s)
      (fun g => f (sigmaAdelicAct K L D σ g)) := by
  intro b hb g
  show f (sigmaAdelicAct K L D σ (b * g)) = _
  rw [map_mul, hf _ (sigmaAdelicAct_mem_adelicBorel D σ hb) _]
  obtain ⟨h1, h2⟩ := borelDiag_sigmaAdelicAct D σ hb
  rw [h1, h2, etaFst_apply, etaFst_apply, etaSnd_apply, etaSnd_apply, cpowChar_unitsAct K L D σ hα,
    cpowChar_unitsAct K L D σ hα, ← hμ', ← hν']

theorem isKfSmooth_comp (σ : L ≃ₐ[K] L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : IsKfSmooth L f) :
    IsKfSmooth L (fun g => f (sigmaAdelicAct K L (Dg K L) σ g)) :=
  isKfSmooth_twist σ f hf

theorem sigmaAdelicAct_mem_principalLevel_inf (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) {u : AdelicGL2 (𝓞 L) L}
    (hu : u ∈ principalLevel (𝓞 L) L
        (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
      finiteAdelicGL2Subgroup L) :
    sigmaAdelicAct K L (Dg K L) σ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hl, hm⟩ := (mem_principalLevel_iff _ _ _).1 hu1
  refine Subgroup.mem_inf.2 ⟨(mem_principalLevel_iff _ _ _).2 ⟨sigmaAdelicAct_mem_levelOne σ N hl, ?_⟩,
    sigmaAdelicAct_mem_finiteAdelicGL2Subgroup σ hu2⟩
  obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.1 hm
  refine Subgroup.mem_map.2 ⟨sigmaAdelicAct K L (Dg K L) σ x, sigmaAdelicAct_mem_levelOne σ N hx, ?_⟩
  rw [← hxu]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, sigmaAdelicAct_weyl]

theorem level_comp (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (f : AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, f (g * u) = f g)
    (g u : AdelicGL2 (𝓞 L) L)
    (hu : u ∈ principalLevel (𝓞 L) L
        (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
      finiteAdelicGL2Subgroup L) :
    f (sigmaAdelicAct K L (Dg K L) σ (g * u)) = f (sigmaAdelicAct K L (Dg K L) σ g) := by
  rw [map_mul]
  exact hf _ _ (sigmaAdelicAct_mem_principalLevel_inf σ N hu)

theorem eisensteinSum_comp (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    ∑' ξ : L, f (sigmaAdelicAct K L D σ (adelicWeyl (𝓞 L) L
        * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) =
      ∑' ξ : L, f (adelicWeyl (𝓞 L) L * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) *
        sigmaAdelicAct K L D σ g) := by
  have h : ∀ ξ : L, f (sigmaAdelicAct K L D σ (adelicWeyl (𝓞 L) L
        * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) =
      (fun η : L => f (adelicWeyl (𝓞 L) L * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) η) *
        sigmaAdelicAct K L D σ g)) ((σ : L ≃ L) ξ) := by
    intro ξ
    simp only [map_mul, sigmaAdelicAct_adelicWeyl, sigmaAdelicAct_unipotentGL2_algebraMap]
    rfl
  simp_rw [h]
  exact Equiv.tsum_eq (σ : L ≃ L) (fun η : L => f (adelicWeyl (𝓞 L) L *
    unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) η) * sigmaAdelicAct K L D σ g))

end Clauses

section MeasureClauses

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem weylIntertwiningIntegral_comp (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (fun x => f (sigmaAdelicAct K L D σ x)) g =
      weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) f (sigmaAdelicAct K L D σ g) := by
  unfold weylIntertwiningIntegral
  have h : ∀ x : AdeleRing (𝓞 L) L,
      f (sigmaAdelicAct K L D σ ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 x * g)) =
        (fun y : AdeleRing (𝓞 L) L => f ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 y * sigmaAdelicAct K L D σ g))
          ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) x) := by
    intro x
    simp only [map_mul, map_inv, sigmaAdelicAct_adelicWeyl, sigmaAdelicAct_unipotentGL2]
  simp_rw [h]
  exact (measurePreserving_act D σ).integral_comp (actHomeo D σ).measurableEmbedding
    (fun y : AdeleRing (𝓞 L) L => f ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 y * sigmaAdelicAct K L D σ g))

end MeasureClauses

end R4SecTransEngine

end

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

open AutomorphicForm R4SecTransEngine in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (N : Ideal (𝓞 L)) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, μ' z = μ (D.unitsAct σ.symm z))
      (_hν' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ν' z = ν (D.unitsAct σ.symm z))
      (ψf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite L (ψf s))
      (_hψff : ∀ s, IsKfSmooth L (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        ψf s (k : AdelicGL2 (𝓞 L) L) = ψf 0 (k : AdelicGL2 (𝓞 L) L))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ψf s (g * u) = ψf s g)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s g = ψf s g + ∑' ξ : L, ψf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (ψf s) g)),
    (∀ s, IsInducedSection (𝓞 L) L (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s)
      (fun g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g))) ∧
    (∀ s, IsArchKFinite L (fun g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g))) ∧
    (∀ s, IsKfSmooth L (fun g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 (AutomorphicForm.sigmaAdelicAct K L D σ.symm p.2)) ∧
    (∀ g : AdelicGL2 (𝓞 L) L, Differentiable ℂ (fun s => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g))) ∧
    (∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm (g * (k : AdelicGL2 (𝓞 L) L)))) ∈ W) ∧
    (∀ (s : ℂ) (k : adelicMaximalCompact L),
      ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L)) = ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
      ∀ u ∈ principalLevel (𝓞 L) L (N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ.symm : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L, ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm (g * u)) = ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) ∧
    (IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 (AutomorphicForm.sigmaAdelicAct K L D σ.symm p.2)) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 (AutomorphicForm.sigmaAdelicAct K L D σ.symm p.2)) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g) = ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g) + ∑' ξ : L, ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g))) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g) =
          weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (fun g => ψf s (AutomorphicForm.sigmaAdelicAct K L D σ.symm g)) g)) := by
  intro αm hαm μ ν μ' ν' hμ' hν' ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat hψflev Oψ Eψ Nψ hEψ
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  have hD : D = Dg K L := Subsingleton.elim _ _
  subst hD
  obtain ⟨hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEf, hNf⟩ := hEψ
  have hcont : Continuous (sigmaAdelicAct K L (Dg K L) σ.symm) := continuous_sigmaAdelicAct K L (Dg K L) σ.symm
  have hcont2 : Continuous fun p : ℂ × AdelicGL2 (𝓞 L) L => (p.1, sigmaAdelicAct K L (Dg K L) σ.symm p.2) :=
    continuous_fst.prodMk (hcont.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℂ × AdelicGL2 (𝓞 L) L => (p.1, sigmaAdelicAct K L (Dg K L) σ.symm p.2))
      (Oψ ×ˢ Set.univ) (Oψ ×ˢ Set.univ) := fun p hp => ⟨hp.1, Set.mem_univ _⟩
  refine ⟨fun s => isInducedSection_comp (Dg K L) σ.symm hαm μ ν μ' ν' hμ' hν' s (ψf s) (hψf s),
    fun s => isArchKFinite_comp σ.symm (ψf s) (hψfK s),
    fun s => isKfSmooth_comp σ.symm (ψf s) (hψff s),
    hψfjc.comp hcont2,
    fun g => hψfhol _,
    fun w => uniformSpan_comp σ.symm ψf hψfKu w,
    fun s k => hψflat s ⟨_, sigmaAdelicAct_mem_adelicMaximalCompact σ.symm k.2⟩,
    fun s g u hu => level_comp σ.symm N (ψf s) (hψflev s) g u hu,
    hO, hOc, hax, hhalf, fun g => hEan _, fun g => hNan _,
    hEc.comp hcont2.continuousOn hmaps, hNc.comp hcont2.continuousOn hmaps,
    fun s hs g => ?_, fun s hs g => ?_⟩
  · rw [hEf s hs, eisensteinSum_comp]
  · rw [hNf s hs, weylIntertwiningIntegral_comp]

end S_AutomorphicForm_isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_and_isArchKFinite_and_axis_continuation_comp_sigmaAdelicAct_symm_of_flat_family_of_principalLevel (solution)
