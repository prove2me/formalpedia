-- Prove2me | solution 1 for AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fb57d011-db39-5acc-9ee4-259bb4e469df

import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos

open NumberField AutomorphicForm.WindowedSiegel
open AutomorphicForm MeasureTheory NumberField.AdelicHaar

noncomputable section

namespace WindowTransport

variable {K : Type} [Field K] [NumberField K]

private theorem measurableSet_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    (letI := glBorel (Fin 2) (𝓞 K) K;
      MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) := by
  letI := glBorel (Fin 2) (𝓞 K) K
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet K c u d₁ d₂
      = (· * x⁻¹) ⁻¹' centreCutSiegelSet K c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet c u d₁ d₂)

private theorem window_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    (letI := glBorel (Fin 2) (𝓞 K) K;
      adelicGLHaar (Fin 2) (𝓞 K) K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 K) K
  calc adelicGLHaar (Fin 2) (𝓞 K) K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      ≤ ∑ x ∈ T, adelicGLHaar (Fin 2) (𝓞 K) K ((· * x) '' centreCutSiegelSet K c u d₁ d₂) :=
        measure_biUnion_finset_le _ _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ =>
        adelicGLHaar_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x

private theorem memLp_window {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hb : IsBoundedOnSiegelWindows K φ) {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁)
    (d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    (letI := glBorel (Fin 2) (𝓞 K) K;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))) := by
  letI := glBorel (Fin 2) (𝓞 K) K
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  obtain ⟨C, hC⟩ := hb c u d₁ d₂ T hc hd₁
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) :=
    isFiniteMeasure_restrict.mpr (window_lt_top hc u hd₁ d₂ T).ne
  exact MemLp.of_bound hφ.aestronglyMeasurable C
    (ae_restrict_of_forall_mem (measurableSet_window c u d₁ d₂ T) hC)

private theorem isAutomorphicFnAt_window {D : Set (AdelicGL2 (𝓞 K) K)}
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (ξ : (productionPinsOf K D U gen B).Z →* ℂˣ) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hb : IsBoundedOnSiegelWindows K φ) {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) (h : IsAutomorphicFnAt K (productionPinsOf K D U gen B) ξ φ) :
    IsAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ξ φ := by
  have h1 := (@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _ (productionPinsOf K D U gen B).mS
    (productionPinsOf K D U gen B).μ (productionPinsOf K D U gen B).Z ξ D φ).1 h
  exact (@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _
    (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B).mS
    (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B).μ
    (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B).Z ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) φ).2
    ⟨h1.1, memLp_window hφ hb hc u hd₁ d₂ T⟩

private theorem realizable_window {D : Set (AdelicGL2 (𝓞 K) K)}
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsBoundedGenuineCuspRealizable K (productionPinsOf K D U gen B) ψ Φ)
    {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    IsBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ψ Φ := by
  obtain ⟨R, hR⟩ := hΦ
  refine ⟨{ toFun := R.toFun
            exists_ne_zero := R.exists_ne_zero
            centralChar := R.centralChar
            smoothCusp := ⟨⟨isAutomorphicFnAt_window U gen B R.centralChar
              hR.isBoundedGenuineFn.continuous hR.isBoundedOnSiegelWindows hc u hd₁ d₂ T
              R.smoothCusp.1.1, R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
            level_invariant := R.level_invariant
            exceptionalSet := R.exceptionalSet
            hecke_eigen := R.hecke_eigen
            central_eigen := R.central_eigen }, ?_⟩
  exact IsBoundedGenuineCuspRealizationAt.of_toFun_eq_productionPinsOf hR rfl

end WindowTransport

end

open WindowTransport in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithBoundedGenuineCuspRealizable K (productionPinsOf K D U gen B)
      (StandardAddChar.stdAddChar K) Φ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsArithBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B)
      (StandardAddChar.stdAddChar K) Φ :=
  realizable_window U gen B (StandardAddChar.stdAddChar K) Φ.toRawCentral hΦ hc u hd₁ d₂ T

end S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
end P2MW
export P2MW.S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos (solution)
