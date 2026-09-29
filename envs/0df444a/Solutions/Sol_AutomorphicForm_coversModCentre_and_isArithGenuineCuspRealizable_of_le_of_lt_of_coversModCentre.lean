-- Prove2me | solution 1 for AutomorphicForm.coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/59e2a900-7cf8-5aa7-a8f9-41cb50ff5c3b

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.AdelicVolume NumberField.AdelicCentre AutomorphicForm MeasureTheory

noncomputable section

namespace DetBandTransport

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
private theorem exists_unit_norm_eq (w : InfinitePlace K) {t : ℝ} (ht : 0 < t) :
    ∃ a : (w.Completion)ˣ, ‖(a : w.Completion)‖ = t := by
  rcases w.isReal_or_isComplex with hw | hw
  · set a₀ : w.Completion := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t with ha₀
    have hna : ‖a₀‖ = t := by
      have h1 := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) a₀
      rw [← h1, ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, ha₀,
        RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos ht]
    have hpos : 0 < ‖a₀‖ := by rw [hna]; exact ht
    exact ⟨Units.mk0 a₀ (norm_pos_iff.mp hpos), by rw [Units.val_mk0]; exact hna⟩
  · set a₀ : w.Completion := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (t : ℂ) with ha₀
    have hna : ‖a₀‖ = t := by
      have h1 := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) a₀
      rw [← h1, ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hw, ha₀,
        RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hpos : 0 < ‖a₀‖ := by rw [hna]; exact ht
    exact ⟨Units.mk0 a₀ (norm_pos_iff.mp hpos), by rw [Units.val_mk0]; exact hna⟩

private theorem archComponent_acu_of_ne (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace K} (hw : w ≠ w₀) :
    archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K (archCentralUnit K w₀ a))) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_one, Matrix.one_apply]
  simp only [archComponent_apply, glArch_apply]
  split_ifs with h
  · subst h
    rw [centralScalar_apply_eq]
    exact archCentralUnit_fst_of_ne w₀ a hw
  · rw [centralScalar_apply_ne _ h]
    rfl

private theorem archDetNorm_acu_of_ne (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace K} (hw : w ≠ w₀) (X : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (centralScalar (𝓞 K) K (archCentralUnit K w₀ a) * X) = archDetNorm w X := by
  unfold archDetNorm
  rw [map_mul, map_mul, archComponent_acu_of_ne w₀ a hw, one_mul]

private theorem exists_central_adjust {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ centreCutSiegelSet K c u d₁ d₂) (S : Finset (InfinitePlace K)) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, centralScalar (𝓞 K) K z * h ∈ centreCutSiegelSet K c u d₁ d₂ ∧
      ∀ w ∈ S, archDetNorm w (centralScalar (𝓞 K) K z * h) ∈ Set.Icc d₁' d₂ := by
  classical
  refine Finset.induction_on S ⟨1, by rw [map_one, one_mul]; exact hh, fun w hw => absurd hw (by simp)⟩ ?_
  intro w₀ S hw₀S ih
  obtain ⟨z, hzW, hzS⟩ := ih
  set X := centralScalar (𝓞 K) K z * h with hX
  have hN : 0 < archDetNorm w₀ X := archDetNorm_pos w₀ X
  have hd₂ : 0 < d₂ := lt_of_lt_of_le hN ((mem_centreCutSiegelSet_iff.1 hzW).2.2.2 w₀).2
  obtain ⟨a, hna⟩ := exists_unit_norm_eq w₀ (Real.sqrt_pos.2 (div_pos hd₂ hN))
  have hsq : ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ * archDetNorm w₀ X = d₂ := by
    rw [hna, Real.mul_self_sqrt (div_pos hd₂ hN).le, div_mul_cancel₀ _ hN.ne']
  have hprod : centralScalar (𝓞 K) K (archCentralUnit K w₀ a * z) * h
      = centralScalar (𝓞 K) K (archCentralUnit K w₀ a) * X := by
    rw [map_mul, mul_assoc]
  have h00 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 0 0
  have h01 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 0 1
  have h10 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 1 0
  have h11 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 1 1
  rw [if_pos rfl] at h00 h11
  rw [if_neg (by decide)] at h01 h10
  refine ⟨archCentralUnit K w₀ a * z, ?_, ?_⟩
  · rw [hprod, mem_centreCutSiegelSet_iff]
    obtain ⟨hfin, hht, hxw, hdet⟩ := mem_centreCutSiegelSet_iff.1 hzW
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_mul, glFin_centralScalar_archCentralUnit, one_mul]; exact hfin
    · intro w
      by_cases hw : w = w₀
      · subst hw
        rw [map_mul, map_mul, localHeight_scalar_entries_mul a.ne_zero h00 h01 h10 h11]
        exact hht w
      · rw [map_mul, map_mul, archComponent_acu_of_ne w₀ a hw, one_mul]; exact hht w
    · intro w
      by_cases hw : w = w₀
      · subst hw
        rw [map_mul, map_mul, xWindowSq_scalar_entries_mul a.ne_zero h00 h01 h10 h11]
        exact hxw w
      · rw [map_mul, map_mul, archComponent_acu_of_ne w₀ a hw, one_mul]; exact hxw w
    · intro w
      by_cases hw : w = w₀
      · subst hw
        rw [archDetNorm_centralScalar_mul, hsq]
        exact ⟨hle.trans hlt.le, le_rfl⟩
      · rw [archDetNorm_acu_of_ne w₀ a hw]; exact hdet w
  · intro w hw
    rw [hprod]
    rcases Finset.mem_insert.1 hw with rfl | hwS
    · rw [archDetNorm_centralScalar_mul, hsq]
      exact ⟨hlt.le, le_rfl⟩
    · have hne : w ≠ w₀ := fun e => hw₀S (e ▸ hwS)
      rw [archDetNorm_acu_of_ne w₀ a hne]
      exact hzS w hwS

private theorem window_mono {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') :
    centreCutSiegelSet K c u d₁' d₂ ⊆ centreCutSiegelSet K c u d₁ d₂ := fun g hg => by
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  exact ⟨hg.1, hg.2.1, hg.2.2.1, fun w => Set.Icc_subset_Icc hle le_rfl (hg.2.2.2 w)⟩

private theorem covers_narrow {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) :
    CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂) := by
  intro g
  obtain ⟨γ, z₀, hmem⟩ := hcov g
  obtain ⟨x, hx, h, hh, hhx⟩ := Set.mem_iUnion₂.1 hmem
  obtain ⟨z₁, hz₁W, hz₁S⟩ := exists_central_adjust hle hlt h hh Finset.univ
  have hnarrow : centralScalar (𝓞 K) K z₁ * h ∈ centreCutSiegelSet K c u d₁' d₂ := by
    rw [mem_centreCutSiegelSet_iff]
    obtain ⟨hfin, hht, hxw, _⟩ := mem_centreCutSiegelSet_iff.1 hz₁W
    exact ⟨hfin, hht, hxw, fun w => hz₁S w (Finset.mem_univ w)⟩
  refine ⟨γ, z₀ * z₁, Set.mem_iUnion₂.2 ⟨x, hx, centralScalar (𝓞 K) K z₁ * h, hnarrow, ?_⟩⟩
  show centralScalar (𝓞 K) K z₁ * h * x = _
  have hhx' : h * x = globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z₀ := hhx
  rw [map_mul, ← mul_assoc, ← hhx', mul_assoc, ← mul_centralScalar_comm]

private theorem isAutomorphicFnAt_of_subset {D D' : Set (AdelicGL2 (𝓞 K) K)} (hDD' : D' ⊆ D)
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (ξ : (productionPinsOf K D U gen B).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsAutomorphicFnAt K (productionPinsOf K D U gen B) ξ φ) :
    IsAutomorphicFnAt K (productionPinsOf K D' U gen B) ξ φ := by
  have h1 := (@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _ (productionPinsOf K D U gen B).mS
    (productionPinsOf K D U gen B).μ (productionPinsOf K D U gen B).Z ξ D φ).1 hφ
  exact (@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _ (productionPinsOf K D' U gen B).mS
    (productionPinsOf K D' U gen B).μ (productionPinsOf K D' U gen B).Z ξ D' φ).2
    ⟨h1.1, h1.2.mono_measure (Measure.restrict_mono hDD' le_rfl)⟩

private theorem realizable_of_subset {D D' : Set (AdelicGL2 (𝓞 K) K)} (hDD' : D' ⊆ D)
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (Φ : HeckeEigensystem K ℂ) (hΦ : IsArithGenuineCuspRealizable K (productionPinsOf K D U gen B) Φ) :
    IsArithGenuineCuspRealizable K (productionPinsOf K D' U gen B) Φ := by
  obtain ⟨R, hR⟩ := hΦ
  exact ⟨{ toFun := R.toFun
           exists_ne_zero := R.exists_ne_zero
           centralChar := R.centralChar
           smoothCusp := ⟨⟨isAutomorphicFnAt_of_subset hDD' U gen B R.centralChar R.toFun R.smoothCusp.1.1,
             R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
           level_invariant := R.level_invariant
           exceptionalSet := R.exceptionalSet
           hecke_eigen := R.hecke_eigen
           central_eigen := R.central_eigen }, hR⟩

end DetBandTransport

end

open DetBandTransport in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Φ) :
    CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂) ∧
      IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) Φ := by
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂)
      ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂ :=
    Set.iUnion₂_mono fun x _ => Set.image_mono (window_mono hle)
  exact ⟨covers_narrow hle hlt T hcov, realizable_of_subset hsub _ _ _ Φ hΦ⟩

end S_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre (solution)
