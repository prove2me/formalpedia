-- Prove2me | solution 1 for AutomorphicForm.coversModCentre_iUnion_centreCutSiegelSet_of_detWindow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e300da83-ec9d-5c1e-a42e-1358a05594b5

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow

set_option autoImplicit false

noncomputable section

namespace Ws23
namespace V2A

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem exists_norm_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 ≤ r) : ∃ a : v.Completion, ‖a‖ = r := by
  rcases v.isReal_or_isComplex with hv | hv
  · obtain ⟨a, ha⟩ := Completion.surjective_extensionEmbeddingOfIsReal hv r
    refine ⟨a, ?_⟩
    rw [← (Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) a, ha,
      Real.norm_of_nonneg hr]
  · obtain ⟨a, ha⟩ := Completion.surjective_extensionEmbedding_of_isComplex hv (r : ℂ)
    refine ⟨a, ?_⟩
    rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) a, ha,
      Complex.norm_real, Real.norm_of_nonneg hr]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * h = h * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _) _).eq

theorem archDetNorm_centralScalar_mul' (v : InfinitePlace F) (w : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F w * g)
      = (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  set s := archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then (w : AdeleRing (𝓞 F) F).1 v else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

theorem centralScalar_mul_mem_centreCutSiegelSet {c u d₁ d₂ e₁ e₂ : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (hdet : ∀ v : InfinitePlace F,
      (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g ∈ Set.Icc e₁ e₂) :
    centralScalar (𝓞 F) F w * g ∈ centreCutSiegelSet F c u e₁ e₂ := by
  obtain ⟨h1, h2, h3, -⟩ := hg
  set s := centralScalar (𝓞 F) F w with hs
  have h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w := centralScalar_apply_eq w 0
  have h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 := centralScalar_apply_ne w (by decide)
  have h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := centralScalar_apply_ne w (by decide)
  have h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w := centralScalar_apply_eq w 1
  have hglFin : glFin (𝓞 F) F s = 1 := glFin_scalar_eq_one F hwf h00 h01 h10 h11
  have hcomp00 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 0 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h00]
  have hcomp01 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 1 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h01]; rfl
  have hcomp10 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h10]; rfl
  have hcomp11 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 1 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h11]
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [map_mul, hglFin, one_mul]
    exact h1
  · rw [map_mul, map_mul, localHeight_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h2 v
  · rw [map_mul, map_mul, xWindowSq_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h3 v
  · rw [hs, archDetNorm_centralScalar_mul']
    exact hdet v

end Ws23.V2A

end

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering in

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ e₁ e₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (he₂ : 0 < e₂) (he : e₁ ≤ e₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u e₁ e₂) := by
  classical
  intro g
  obtain ⟨γ, z, hmem⟩ := hcov g
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨x, hx, s, hs, hsx⟩ := hmem

  have hδ : ∀ v : InfinitePlace F, 0 < AdelicVolume.archDetNorm v s := fun v => AdelicVolume.archDetNorm_pos v s
  choose a ha using fun v : InfinitePlace F =>
    Ws23.V2A.exists_norm_eq v (Real.sqrt_nonneg (e₂ / AdelicVolume.archDetNorm v s))
  have ha0 : ∀ v, a v ≠ 0 := fun v => by
    rw [← norm_pos_iff, ha]
    exact Real.sqrt_pos.mpr (div_pos he₂ (hδ v))
  let wz : (AdeleRing (𝓞 F) F)ˣ :=
    { val := ((fun v => a v : InfiniteAdeleRing F), 1)
      inv := ((fun v => (a v)⁻¹ : InfiniteAdeleRing F), 1)
      val_inv := by
        refine Prod.ext (funext fun v => ?_) (one_mul 1)
        show a v * (a v)⁻¹ = 1
        exact mul_inv_cancel₀ (ha0 v)
      inv_val := by
        refine Prod.ext (funext fun v => ?_) (one_mul 1)
        show (a v)⁻¹ * a v = 1
        exact inv_mul_cancel₀ (ha0 v) }
  have hwf : (wz : AdeleRing (𝓞 F) F).2 = 1 := rfl
  have hwa : ∀ v : InfinitePlace F, (wz : AdeleRing (𝓞 F) F).1 v ≠ 0 := ha0
  have hmem' : centralScalar (𝓞 F) F wz * s ∈ centreCutSiegelSet F c u e₁ e₂ := by
    refine Ws23.V2A.centralScalar_mul_mem_centreCutSiegelSet hwf hwa hs fun v => ?_
    have hv : (‖(wz : AdeleRing (𝓞 F) F).1 v‖ * ‖(wz : AdeleRing (𝓞 F) F).1 v‖) * AdelicVolume.archDetNorm v s = e₂ := by
      show (‖a v‖ * ‖a v‖) * AdelicVolume.archDetNorm v s = e₂
      rw [ha, Real.mul_self_sqrt (div_pos he₂ (hδ v)).le, div_mul_cancel₀ _ (hδ v).ne']
    rw [hv]
    exact ⟨he, le_rfl⟩
  refine ⟨γ, z * wz, ?_⟩
  rw [map_mul, ← mul_assoc, ← hsx, mul_assoc s x, ← Ws23.V2A.centralScalar_mul_comm wz x, ← mul_assoc,
    ← Ws23.V2A.centralScalar_mul_comm wz s]
  exact Set.mem_iUnion₂.mpr ⟨x, hx, _, hmem', rfl⟩

end S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow
end P2MW
export P2MW.S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow (solution)
