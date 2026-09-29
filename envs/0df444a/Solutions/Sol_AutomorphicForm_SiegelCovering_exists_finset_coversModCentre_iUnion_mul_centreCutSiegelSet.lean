-- Prove2me | solution 1 for AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/724c0284-b66a-5f95-8062-f675fa367bee

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
import Theorems.Thm_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet

open NumberField IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction NumberField.AdelicLevel NumberField.AdelicHeight NumberField.InfinitePlace

p2m_open_scoped "NumberField NumberField.InfinitePlace.NumberField"

noncomputable section

namespace SiegelCoveringGeneral

section Local

variable {K : Type*} [NormedField K]

private theorem coe_mul_eq (s g : GL (Fin 2) K) :
    ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

private theorem bottom_upper_entries_mul {s : GL (Fin 2) K} {t : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t) (g : GL (Fin 2) K) (j : Fin 2) :
    ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j
      = t * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
  ring

private theorem rowMaxNorm_upper_entries_mul {s : GL (Fin 2) K} {t : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t) (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖t‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [bottom_upper_entries_mul h10 h11 g 0, bottom_upper_entries_mul h10 h11 g 1, norm_mul,
    norm_mul, mul_max_of_nonneg _ _ (norm_nonneg t)]

private theorem finLocalHeight_upper_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t) (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = ‖a‖ / ‖t‖ * finLocalHeight g := by
  have ht0 : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  unfold finLocalHeight
  rw [det_upper_entries_mul h00 h10 h11 g, rowMaxNorm_upper_entries_mul h10 h11 g, norm_mul,
    norm_mul, div_mul_div_comm]
  have h1 : ‖a‖ * ‖t‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖t‖ * (‖a‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖) := by ring
  have h2 : (‖t‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)) ^ 2
      = ‖t‖ * (‖t‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2) := by ring
  rw [h1, h2, mul_div_mul_left _ _ ht0.ne']

private theorem finLocalHeight_mul_scalar_entries {g z : GL (Fin 2) K} {c : K} (hc : c ≠ 0)
    (h00 : (z : Matrix (Fin 2) (Fin 2) K) 0 0 = c)
    (h01 : (z : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (z : Matrix (Fin 2) (Fin 2) K) 1 1 = c) :
    finLocalHeight (g * z) = finLocalHeight g := by
  have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  have hb0 : ((g * z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0
      = (g : Matrix (Fin 2) (Fin 2) K) 1 0 * c := by
    rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h00, h10]
    ring
  have hb1 : ((g * z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
      = (g : Matrix (Fin 2) (Fin 2) K) 1 1 * c := by
    rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    ring
  have hdet : ((g * z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = (g : Matrix (Fin 2) (Fin 2) K).det * (c * c) := by
    rw [coe_mul_eq, Matrix.det_mul]
    congr 1
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  unfold finLocalHeight rowMaxNorm
  rw [hdet, hb0, hb1]
  simp only [norm_mul]
  rw [← max_mul_of_nonneg _ _ (norm_nonneg c)]
  have h2 : (max ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ * ‖c‖) ^ 2
      = (‖c‖ * ‖c‖) *
          max ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 := by
    ring
  rw [h2, mul_comm ‖(g : Matrix (Fin 2) (Fin 2) K).det‖, mul_div_mul_left _ _ (mul_pos hc0 hc0).ne']

private theorem piece_bound_real {d x y c : ℝ} (hd : 0 ≤ d) (hy : 0 ≤ y) (hc : 0 < c)
    (hr : 0 < max x y) :
    d * c / max (x * c) y ^ 2 ≤ d / max x y ^ 2 * max c c⁻¹ := by
  rcases le_total x y with hxy | hyx
  · have hy0 : 0 < y := by rwa [max_eq_right hxy] at hr
    calc d * c / max (x * c) y ^ 2 ≤ d * c / y ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg hd hc.le) (pow_pos hy0 2)
            (pow_le_pow_left₀ hy (le_max_right _ _) 2)
      _ = d / max x y ^ 2 * c := by rw [max_eq_right hxy]; ring
      _ ≤ d / max x y ^ 2 * max c c⁻¹ :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (div_nonneg hd (pow_nonneg (hr.le) 2))
  · have hx0 : 0 < x := by rwa [max_eq_left hyx] at hr
    have hxc : 0 < x * c := mul_pos hx0 hc
    calc d * c / max (x * c) y ^ 2 ≤ d * c / (x * c) ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg hd hc.le) (pow_pos hxc 2)
            (pow_le_pow_left₀ hxc.le (le_max_left _ _) 2)
      _ = d / max x y ^ 2 * c⁻¹ := by
          have hx' : x ≠ 0 := hx0.ne'
          have hc' : c ≠ 0 := hc.ne'
          rw [max_eq_left hyx]
          field_simp
      _ ≤ d / max x y ^ 2 * max c c⁻¹ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg hd (pow_nonneg (hr.le) 2))

private theorem finLocalHeight_mul_diag_entries_le (m : GL (Fin 2) K) {D : GL (Fin 2) K} {c : K}
    (hc : c ≠ 0)
    (h00 : (D : Matrix (Fin 2) (Fin 2) K) 0 0 = c)
    (h01 : (D : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (D : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (D : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) :
    finLocalHeight (m * D) ≤ finLocalHeight m * max ‖c‖ ‖c‖⁻¹ := by
  have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  have hb0 : ((m * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0
      = (m : Matrix (Fin 2) (Fin 2) K) 1 0 * c := by
    rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h00, h10]
    ring
  have hb1 : ((m * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
      = (m : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    ring
  have hdet : ((m * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = (m : Matrix (Fin 2) (Fin 2) K).det * c := by
    rw [coe_mul_eq, Matrix.det_mul]
    congr 1
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hr := rowMaxNorm_pos m
  unfold rowMaxNorm at hr
  unfold finLocalHeight rowMaxNorm
  rw [hdet, hb0, hb1, norm_mul, norm_mul]
  exact piece_bound_real (norm_nonneg _) (norm_nonneg _) hc0 hr

end Local

section Adelic

variable {F : Type} [Field F] [NumberField F]

private theorem adelicHeight_globalPoints_upper_mul (b : GL (Fin 2) F)
    (hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (globalPoints (𝓞 F) F b * g) = adelicHeight F g := by
  obtain ⟨α, hα⟩ : ∃ α : F, (b : Matrix (Fin 2) (Fin 2) F) 0 0 = α := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : F, (b : Matrix (Fin 2) (Fin 2) F) 1 1 = δ := ⟨_, rfl⟩
  have hdet : (b : Matrix (Fin 2) (Fin 2) F).det = α * δ := by
    rw [Matrix.det_fin_two, hα, hδ, hb, mul_zero, sub_zero]
  have hαδ : α * δ ≠ 0 := by
    rw [← hdet]
    exact (Matrix.isUnits_det_units b).ne_zero
  have hα0 : α ≠ 0 := left_ne_zero_of_mul hαδ
  have hδ0 : δ ≠ 0 := right_ne_zero_of_mul hαδ

  have harch : archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g))
      = (∏ w : InfinitePlace F, w α ^ w.mult) / (∏ w : InfinitePlace F, w δ ^ w.mult)
          * archHeight F (glArch (𝓞 F) F g) := by
    have hplace : ∀ w : InfinitePlace F,
        localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g)))
          = w α / w δ * localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
      intro w
      have h00w : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F b)) :
          GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0
            = (α : w.Completion) := by
        rw [archComponent_globalPoints_apply, hα]
      have h11w : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F b)) :
          GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1
            = (δ : w.Completion) := by
        rw [archComponent_globalPoints_apply, hδ]
      have h10w : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F b)) :
          GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
        rw [← norm_eq_zero, archComponent_globalPoints_apply, norm_coe_completion, hb, map_zero]
      have hδw : (δ : w.Completion) ≠ 0 := by
        rw [← norm_pos_iff, norm_coe_completion]
        exact InfinitePlace.pos_iff.mpr hδ0
      rw [map_mul, map_mul, localHeight_upper_entries_mul hδw h00w h10w h11w, norm_coe_completion,
        norm_coe_completion]
    unfold archHeight
    calc ∏ w : InfinitePlace F,
            localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g))) ^ w.mult
        = ∏ w : InfinitePlace F,
            ((w α ^ w.mult / w δ ^ w.mult)
              * localHeight (archComponent F w (glArch (𝓞 F) F g)) ^ w.mult) := by
          refine Finset.prod_congr rfl fun w _ => ?_
          rw [hplace w, mul_pow, div_pow]
      _ = (∏ w : InfinitePlace F, w α ^ w.mult / w δ ^ w.mult)
            * ∏ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ^ w.mult := by
          rw [Finset.prod_mul_distrib]
      _ = (∏ w : InfinitePlace F, w α ^ w.mult) / (∏ w : InfinitePlace F, w δ ^ w.mult)
            * ∏ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ^ w.mult := by
          rw [Finset.prod_div_distrib]

  have hfin : finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F b * g))
      = (∏ᶠ w : FinitePlace F, w α) / (∏ᶠ w : FinitePlace F, w δ)
          * finHeight F (glFin (𝓞 F) F g) := by
    have hplace : ∀ v : HeightOneSpectrum (𝓞 F),
        finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F b * g)))
          = ‖FinitePlace.embedding v α‖ / ‖FinitePlace.embedding v δ‖
            * finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) := by
      intro v
      have h00v : ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F b)) :
          GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
            = FinitePlace.embedding v α := by
        rw [finComponent_globalPoints_apply, hα]
      have h11v : ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F b)) :
          GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
            = FinitePlace.embedding v δ := by
        rw [finComponent_globalPoints_apply, hδ]
      have h10v : ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F b)) :
          GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
            = 0 := by
        rw [finComponent_globalPoints_apply, hb, map_zero]
      have hδv : FinitePlace.embedding v δ ≠ 0 := (map_ne_zero _).2 hδ0
      rw [map_mul, map_mul, finLocalHeight_upper_entries_mul hδv h00v h10v h11v]
    have hA := hasFiniteMulSupport_finLocalHeight (glFin (𝓞 F) F g)
    have hnα := hasFiniteMulSupport_norm_embedding (F := F) hα0
    have hnδ := hasFiniteMulSupport_norm_embedding (F := F) hδ0
    have hAB : (fun v : HeightOneSpectrum (𝓞 F) =>
        ‖FinitePlace.embedding v α‖ / ‖FinitePlace.embedding v δ‖).HasFiniteMulSupport :=
      hnα.div hnδ
    unfold finHeight
    calc ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F b * g)))
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            (‖FinitePlace.embedding v α‖ / ‖FinitePlace.embedding v δ‖
              * finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F g))) := finprod_congr hplace
      _ = (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖ / ‖FinitePlace.embedding v δ‖)
            * ∏ᶠ v : HeightOneSpectrum (𝓞 F), finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) :=
          finprod_mul_distrib hAB hA
      _ = (∏ᶠ w : FinitePlace F, w α) / (∏ᶠ w : FinitePlace F, w δ)
            * ∏ᶠ v : HeightOneSpectrum (𝓞 F), finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) := by
          rw [finprod_div_distrib hnα hnδ, finprod_norm_embedding, finprod_norm_embedding]

  have hα1 := prod_abs_eq_one hα0
  have hδ1 := prod_abs_eq_one hδ0
  unfold adelicHeight
  rw [harch, hfin]
  calc (∏ w : InfinitePlace F, w α ^ w.mult) / (∏ w : InfinitePlace F, w δ ^ w.mult)
          * archHeight F (glArch (𝓞 F) F g)
        * ((∏ᶠ w : FinitePlace F, w α) / (∏ᶠ w : FinitePlace F, w δ) * finHeight F (glFin (𝓞 F) F g))
      = ((∏ w : InfinitePlace F, w α ^ w.mult) * ∏ᶠ w : FinitePlace F, w α)
          / ((∏ w : InfinitePlace F, w δ ^ w.mult) * ∏ᶠ w : FinitePlace F, w δ)
          * (archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)) := by ring
    _ = archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g) := by
      rw [hα1, hδ1, div_one, one_mul]

end Adelic

section Piece

variable {F : Type} [Field F] [NumberField F]

private theorem coe_mul_coe_inv_apply (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (a : FiniteAdeleRing (𝓞 F) F) v * ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
      = 1 := by
  rw [← coe_mul_apply, Units.mul_inv, coe_one_apply]

private theorem coe_apply_ne_zero (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (a : FiniteAdeleRing (𝓞 F) F) v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (coe_mul_coe_inv_apply a v)

private def pieceBound (a : (FiniteAdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    max ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖⁻¹

private theorem hasFiniteMulSupport_pieceBound (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) =>
      max ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖⁻¹).HasFiniteMulSupport := by
  refine Filter.eventually_cofinite.mp ?_
  have ha : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (a : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := (a : FiniteAdeleRing (𝓞 F) F).2
  have ha' : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    ((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2
  filter_upwards [ha, ha'] with v hv hv'
  have h1 : ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ≤ 1 := norm_le_one_of_mem_adicCompletionIntegers hv
  have h2 : ‖((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ ≤ 1 :=
    norm_le_one_of_mem_adicCompletionIntegers hv'
  have hprod : ‖(a : FiniteAdeleRing (𝓞 F) F) v‖
      * ‖((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
    rw [← norm_mul, coe_mul_coe_inv_apply, norm_one]
  have h3 : ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : ℝ) = ‖(a : FiniteAdeleRing (𝓞 F) F) v‖
          * ‖((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ := hprod.symm
      _ ≤ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ := mul_one _
  rw [h3, inv_one, max_self]

private theorem pieceBound_pos (a : (FiniteAdeleRing (𝓞 F) F)ˣ) : 0 < pieceBound a := by
  unfold pieceBound
  exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v =>
    lt_max_of_lt_left (norm_pos_iff.2 (coe_apply_ne_zero a v))

private theorem finComponent_finIdeleDiag_apply_zero_zero (a : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (finIdeleDiag F a)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 = (a : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem finComponent_finIdeleDiag_apply_zero_one (a : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (finIdeleDiag F a)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 = 0 := rfl

private theorem finComponent_finIdeleDiag_apply_one_zero (a : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (finIdeleDiag F a)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := rfl

private theorem finComponent_finIdeleDiag_apply_one_one (a : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (finIdeleDiag F a)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 1 := rfl

private theorem finComponent_scalar_apply_zero_zero (s : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (Matrix.GeneralLinearGroup.scalar (Fin 2) s) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
      = (s : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem finComponent_scalar_apply_zero_one (s : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (Matrix.GeneralLinearGroup.scalar (Fin 2) s) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 = 0 := rfl

private theorem finComponent_scalar_apply_one_zero (s : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (Matrix.GeneralLinearGroup.scalar (Fin 2) s) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := rfl

private theorem finComponent_scalar_apply_one_one (s : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (Matrix.GeneralLinearGroup.scalar (Fin 2) s) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = (s : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem finHeight_mul_scalar (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (s : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finHeight F (h * Matrix.GeneralLinearGroup.scalar (Fin 2) s) = finHeight F h := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  exact finLocalHeight_mul_scalar_entries (coe_apply_ne_zero s v)
    (finComponent_scalar_apply_zero_zero s v) (finComponent_scalar_apply_zero_one s v)
    (finComponent_scalar_apply_one_zero s v) (finComponent_scalar_apply_one_one s v)

private theorem finHeight_mul_finIdeleDiag_le {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finHeight F (k * glFin (𝓞 F) F (finIdeleDiag F a)) ≤ pieceBound a := by
  rw [mem_finiteIntegralGL2_iff] at hk
  have hle : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (k * glFin (𝓞 F) F (finIdeleDiag F a)))
        ≤ max ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖⁻¹ := by
    intro v
    have hk1 : finLocalHeight (finComponent (𝓞 F) F v k) = 1 := by
      refine finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
      · rw [finComponent_apply]
        exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
      · rw [← map_inv, finComponent_apply]
        exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)
    rw [map_mul]
    refine (finLocalHeight_mul_diag_entries_le _ (coe_apply_ne_zero a v)
      (finComponent_finIdeleDiag_apply_zero_zero a v) (finComponent_finIdeleDiag_apply_zero_one a v)
      (finComponent_finIdeleDiag_apply_one_zero a v)
      (finComponent_finIdeleDiag_apply_one_one a v)).trans ?_
    rw [hk1, one_mul]
  unfold finHeight pieceBound
  exact finprod_le_finprod (hasFiniteMulSupport_finLocalHeight _) (fun v => (finLocalHeight_pos _).le)
    (hasFiniteMulSupport_pieceBound a) hle

end Piece

section Reduction

private theorem finite_criterion
    (F : Type) [Field F] [NumberField F]
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))
    (a d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hd : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
              ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v)))
    (hcls : AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
      AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
              (AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F b) * g *
            Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
            (AutomorphicForm.finIdeleDiag F a))⁻¹
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers F) F := by
  exact AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2 F g a d hd hcls

private theorem finite_diagonal_reps
    (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ),
      ∀ g : Matrix.GeneralLinearGroup (Fin 2)
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F),
        ∃ a ∈ R, ∃ d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
              max
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
                    ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v))) ∧
          AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
            AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g) := by
  exact AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq F

private theorem exists_finset_forall_exists_upper_mem (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset (FiniteAdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      ∃ a ∈ R, ∃ b : GL (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        ∃ s : (FiniteAdeleRing (𝓞 F) F)ˣ,
          glFin (𝓞 F) F (globalPoints (𝓞 F) F b) * glFin (𝓞 F) F g *
              Matrix.GeneralLinearGroup.scalar (Fin 2) s * (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹
            ∈ finiteIntegralGL2 (𝓞 F) F := by
  obtain ⟨R, hR⟩ := finite_diagonal_reps F
  refine ⟨R, fun g => ?_⟩
  obtain ⟨a, ha, d, hd, hcls⟩ := hR (glFin (𝓞 F) F g)
  obtain ⟨b, hb, s, hmem⟩ := finite_criterion F (glFin (𝓞 F) F g) a d hd hcls
  exact ⟨a, ha, b, hb, s, hmem⟩

private theorem adelicHeight_le_pieceBound_mul_archHeight {F : Type} [Field F] [NumberField F]
    {b : GL (Fin 2) F} (hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {g : AdelicGL2 (𝓞 F) F}
    {s a : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hmem : glFin (𝓞 F) F (globalPoints (𝓞 F) F b) * glFin (𝓞 F) F g *
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹
      ∈ finiteIntegralGL2 (𝓞 F) F) :
    adelicHeight F g
      ≤ pieceBound a * archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g)) := by
  have hfin : finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F b * g)) ≤ pieceBound a := by
    rw [map_mul, ← finHeight_mul_scalar _ s,
      ← inv_mul_cancel_right (glFin (𝓞 F) F (globalPoints (𝓞 F) F b) * glFin (𝓞 F) F g *
        Matrix.GeneralLinearGroup.scalar (Fin 2) s) (glFin (𝓞 F) F (finIdeleDiag F a))]
    exact finHeight_mul_finIdeleDiag_le hmem a
  calc adelicHeight F g = adelicHeight F (globalPoints (𝓞 F) F b * g) :=
        (adelicHeight_globalPoints_upper_mul b hb g).symm
    _ = archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g))
          * finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F b * g)) := rfl
    _ ≤ archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g)) * pieceBound a :=
        mul_le_mul_of_nonneg_left hfin (archHeight_pos F _).le
    _ = pieceBound a * archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F b * g)) := mul_comm _ _

end Reduction

section Floor

section FloorLocal

variable {K : Type*} [NormedField K]

private theorem floor_piece_real {d x y c : ℝ} (hd : 0 ≤ d) (hx : x ≤ 1) (hy : y ≤ 1) (hc : 0 < c)
    (hr : 0 < max (x * c) y) :
    d / max c c⁻¹ ≤ d * c / max (x * c) y ^ 2 := by
  have hle : max (x * c) y ≤ max c 1 :=
    max_le ((mul_le_of_le_one_left hc.le hx).trans (le_max_left _ _))
      (hy.trans (le_max_right _ _))
  have hsq : max c 1 ^ 2 ≤ c * max c c⁻¹ := by
    rcases le_total 1 c with h1c | hc1
    · rw [max_eq_left h1c, sq]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le
    · rw [max_eq_right hc1, one_pow]
      calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
        _ ≤ c * max c c⁻¹ := mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  have hbound : max (x * c) y ^ 2 ≤ c * max c c⁻¹ :=
    (pow_le_pow_left₀ hr.le hle 2).trans hsq
  calc d / max c c⁻¹ = c * d / (c * max c c⁻¹) := (mul_div_mul_left d (max c c⁻¹) hc.ne').symm
    _ = d * c / (c * max c c⁻¹) := by rw [mul_comm c d]
    _ ≤ d * c / max (x * c) y ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hd hc.le) (pow_pos hr 2) hbound

private theorem norm_det_div_le_finLocalHeight_mul_diag (m : GL (Fin 2) K)
    (hm0 : ‖(m : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ 1) (hm1 : ‖(m : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ 1)
    {D : GL (Fin 2) K} {c : K} (hc : c ≠ 0)
    (h00 : (D : Matrix (Fin 2) (Fin 2) K) 0 0 = c)
    (h01 : (D : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (D : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (D : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) :
    ‖(m : Matrix (Fin 2) (Fin 2) K).det‖ / max ‖c‖ ‖c‖⁻¹ ≤ finLocalHeight (m * D) := by
  have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  have hb0 : ((m * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0
      = (m : Matrix (Fin 2) (Fin 2) K) 1 0 * c := by
    rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h00, h10]
    ring
  have hb1 : ((m * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
      = (m : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [coe_mul_eq, Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    ring
  have hdet : ((m * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = (m : Matrix (Fin 2) (Fin 2) K).det * c := by
    rw [coe_mul_eq, Matrix.det_mul]
    congr 1
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hr := rowMaxNorm_pos (m * D)
  unfold rowMaxNorm at hr
  rw [hb0, hb1, norm_mul] at hr
  unfold finLocalHeight rowMaxNorm
  rw [hdet, hb0, hb1, norm_mul, norm_mul]
  exact floor_piece_real (norm_nonneg _) hm0 hm1 hc0 hr

end FloorLocal

section FloorFinite

variable {F : Type} [Field F] [NumberField F]

private theorem algebraMap_algebraMap_mem_integralFiniteAdeles (p : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F p)
      ∈ integralFiniteAdeles (𝓞 F) F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one p

private theorem norm_finComponent_globalPoints_mul_apply_le_one {γ : GL (Fin 2) F} {p q : 𝓞 F}
    (hp : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = algebraMap (𝓞 F) F p)
    (hq : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = algebraMap (𝓞 F) F q)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) (j : Fin 2) :
    ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * k) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 j‖ ≤ 1 := by
  rw [mem_finiteIntegralGL2_iff] at hk
  rw [finComponent_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    glFin_globalPoints_apply, glFin_globalPoints_apply, hp, hq]
  exact norm_le_one_of_mem_adicCompletionIntegers
    (add_mem (mul_mem (algebraMap_algebraMap_mem_integralFiniteAdeles p v) (hk.1 0 j v))
      (mul_mem (algebraMap_algebraMap_mem_integralFiniteAdeles q v) (hk.1 1 j v)))

private theorem one_le_norm_det_finComponent {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    1 ≤ ‖((finComponent (𝓞 F) F v k : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ := by
  rw [mem_finiteIntegralGL2_iff] at hk
  have hinv : ‖(((finComponent (𝓞 F) F v k)⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ ≤ 1 := by
    refine norm_det_le_one fun i j => ?_
    rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)
  have hprod : ‖((finComponent (𝓞 F) F v k : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖
      * ‖(((finComponent (𝓞 F) F v k)⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, norm_one]
  calc (1 : ℝ) = _ := hprod.symm
    _ ≤ ‖((finComponent (𝓞 F) F v k : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ * 1 :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = _ := mul_one _

private theorem norm_embedding_det_div_le_finLocalHeight {γ : GL (Fin 2) F} {p q : 𝓞 F}
    (hp : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = algebraMap (𝓞 F) F p)
    (hq : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = algebraMap (𝓞 F) F q)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F)
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det)‖
        / max ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖⁻¹
      ≤ finLocalHeight (finComponent (𝓞 F) F v
          (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * k * glFin (𝓞 F) F (finIdeleDiag F a))) := by
  have hmax : 0 ≤ max ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖⁻¹ :=
    (norm_nonneg _).trans (le_max_left _ _)
  have hdetle : ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det)‖
      ≤ ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * k) :
          GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ := by
    rw [map_mul, Units.val_mul, Matrix.det_mul, norm_mul, det_finComponent_globalPoints]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_norm_det_finComponent hk v)
  rw [map_mul]
  refine (div_le_div_of_nonneg_right hdetle hmax).trans ?_
  exact norm_det_div_le_finLocalHeight_mul_diag _
    (norm_finComponent_globalPoints_mul_apply_le_one hp hq hk v 0)
    (norm_finComponent_globalPoints_mul_apply_le_one hp hq hk v 1) (coe_apply_ne_zero a v)
    (finComponent_finIdeleDiag_apply_zero_zero a v) (finComponent_finIdeleDiag_apply_zero_one a v)
    (finComponent_finIdeleDiag_apply_one_zero a v) (finComponent_finIdeleDiag_apply_one_one a v)

private theorem finprod_norm_embedding_det_div_le_finHeight {γ : GL (Fin 2) F} {p q : 𝓞 F}
    (hp : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = algebraMap (𝓞 F) F p)
    (hq : (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = algebraMap (𝓞 F) F q)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F)
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det)‖)
        / pieceBound a
      ≤ finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * k * glFin (𝓞 F) F (finIdeleDiag F a)) := by
  have hdet0 : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  rw [div_le_iff₀ (pieceBound_pos a)]
  unfold finHeight pieceBound
  rw [← finprod_mul_distrib (hasFiniteMulSupport_finLocalHeight _) (hasFiniteMulSupport_pieceBound a)]
  refine finprod_le_finprod (hasFiniteMulSupport_norm_embedding hdet0) (fun _ => norm_nonneg _)
    ((hasFiniteMulSupport_finLocalHeight _).mul (hasFiniteMulSupport_pieceBound a)) fun v => ?_
  have hv := norm_embedding_det_div_le_finLocalHeight hp hq hk a v
  have hmax : 0 < max ‖(a : FiniteAdeleRing (𝓞 F) F) v‖ ‖(a : FiniteAdeleRing (𝓞 F) F) v‖⁻¹ :=
    lt_max_of_lt_left (norm_pos_iff.2 (coe_apply_ne_zero a v))
  rwa [div_le_iff₀ hmax] at hv

omit [NumberField F] in

private theorem exists_gl_bottom_row (p q : F) (h : p ≠ 0 ∨ q ≠ 0) :
    ∃ γ : GL (Fin 2) F,
      (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = p ∧ (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = q := by
  rcases h with hp | hq
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; p, q] ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using hp
    · simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; p, q] ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using hq
    · simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

end FloorFinite

end Floor

section FloorArch

open scoped Classical Pointwise

variable {F : Type} [Field F] [NumberField F]

private scoped instance floorArch_countable_isReal : Countable {w : InfinitePlace F // w.IsReal} :=
  inferInstance

private scoped instance floorArch_countable_isComplex : Countable {w : InfinitePlace F // w.IsComplex} :=
  inferInstance

private scoped instance floorArch_secondCountable_mixedSpace :
    SecondCountableTopology (mixedEmbedding.mixedSpace F) :=
  inferInstance

private scoped instance floorArch_borelSpace_mixedSpace : BorelSpace (mixedEmbedding.mixedSpace F) :=
  inferInstance

private scoped instance floorArch_measurableAdd₂_mixedSpace : MeasurableAdd₂ (mixedEmbedding.mixedSpace F) :=
  inferInstance

private scoped instance floorArch_sigmaFinite_mixedSpace :
    MeasureTheory.SigmaFinite
      (MeasureTheory.volume : MeasureTheory.Measure (mixedEmbedding.mixedSpace F)) :=
  inferInstance

private scoped instance floorArch_borelSpace_pi : BorelSpace (Fin 2 → mixedEmbedding.mixedSpace F) :=
  Pi.borelSpace

private scoped instance floorArch_isAddHaarMeasure_pi :
    (MeasureTheory.volume :
      MeasureTheory.Measure (Fin 2 → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
  inferInstance

omit [NumberField F] in

private theorem normAtPlace_ringEquiv_mixedSpace (x : InfiniteAdeleRing F) (w : InfinitePlace F) :
    mixedEmbedding.normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ‖x w‖ := by
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact AutomorphicForm.SiegelCovering.norm_extensionEmbeddingOfIsReal hw (x w)
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw),
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact AutomorphicForm.SiegelCoordinates.norm_extensionEmbedding w (x w)

omit [NumberField F] in

private theorem det_archComponent (w : InfinitePlace F) (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((archComponent F w h : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det
      = (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det w := by
  have hmat : ((archComponent F w h : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = (archEval F w).mapMatrix (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    ext i j
    rfl
  rw [hmat, ← RingHom.map_det]
  rfl

private theorem abs_norm_mixedSpace (x : mixedEmbedding.mixedSpace F) :
    |Algebra.norm ℝ x| = mixedEmbedding.norm x := by
  have hmul : LinearMap.mul ℝ (mixedEmbedding.mixedSpace F) x
      = LinearMap.prodMap
          (LinearMap.pi fun i => (LinearMap.mul ℝ ℝ (x.1 i)).comp (LinearMap.proj i))
          (LinearMap.pi fun j => (LinearMap.mul ℝ ℂ (x.2 j)).comp (LinearMap.proj j)) :=
    LinearMap.ext fun _ => rfl
  have hC : ∀ z : ℂ, LinearMap.det (LinearMap.mul ℝ ℂ z) = Complex.normSq z := fun z =>
    (Algebra.norm_complex_apply z).symm ▸ rfl
  have hR : ∀ r : ℝ, LinearMap.det (LinearMap.mul ℝ ℝ r) = r := fun r => by
    rw [LinearMap.det_ring, LinearMap.mul_apply', mul_one]
  rw [Algebra.norm_apply]
  change |LinearMap.det (LinearMap.mul ℝ (mixedEmbedding.mixedSpace F) x)| = _
  rw [hmul, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [hC, hR]
  rw [abs_mul, Finset.abs_prod, abs_of_nonneg (Finset.prod_nonneg fun j _ => Complex.normSq_nonneg _),
    mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [InfinitePlace.mult_isReal, pow_one, mixedEmbedding.normAtPlace_apply_of_isReal w.2,
      Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [InfinitePlace.mult_isComplex, mixedEmbedding.normAtPlace_apply_of_isComplex w.2,
      Complex.normSq_eq_norm_sq]

private theorem abs_det_vecMul (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :
    |LinearMap.det ((Matrix.toLin' M.transpose).restrictScalars ℝ)| = mixedEmbedding.norm M.det := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose, abs_norm_mixedSpace]

private def archBox (F : Type) [Field F] [NumberField F] (t : ℝ) :
    Set (Fin 2 → mixedEmbedding.mixedSpace F) :=
  {v | ∀ i : Fin 2, ∀ w : InfinitePlace F, mixedEmbedding.normAtPlace w (v i) < t}

private theorem convex_archBox (t : ℝ) : Convex ℝ (archBox F t) := by
  intro v hv v' hv' a b ha hb hab i w
  have h1 := hv i w
  have h2 := hv' i w
  calc mixedEmbedding.normAtPlace w ((a • v + b • v') i)
      = mixedEmbedding.normAtPlace w (a • v i + b • v' i) := rfl
    _ ≤ mixedEmbedding.normAtPlace w (a • v i) + mixedEmbedding.normAtPlace w (b • v' i) :=
        mixedEmbedding.normAtPlace_add_le w _ _
    _ = a * mixedEmbedding.normAtPlace w (v i) + b * mixedEmbedding.normAtPlace w (v' i) := by
        rw [mixedEmbedding.normAtPlace_smul, mixedEmbedding.normAtPlace_smul, abs_of_nonneg ha,
          abs_of_nonneg hb]
    _ < t := by
        rcases eq_or_lt_of_le ha with ha0 | ha0
        · subst ha0
          rw [zero_add] at hab
          subst hab
          simpa using h2
        · rcases eq_or_lt_of_le hb with hb0 | hb0
          · subst hb0
            rw [add_zero] at hab
            subst hab
            simpa using h1
          · calc a * mixedEmbedding.normAtPlace w (v i) + b * mixedEmbedding.normAtPlace w (v' i)
                < a * t + b * t := by gcongr
              _ = t := by rw [← add_mul, hab, one_mul]

private theorem neg_mem_archBox {t : ℝ} {v : Fin 2 → mixedEmbedding.mixedSpace F}
    (hv : v ∈ archBox F t) : -v ∈ archBox F t := by
  intro i w
  have := hv i w
  rwa [Pi.neg_apply, mixedEmbedding.normAtPlace_neg]

private theorem isOpen_archBox (t : ℝ) : IsOpen (archBox F t) := by
  have : archBox F t = ⋂ i : Fin 2, ⋂ w : InfinitePlace F,
      {v : Fin 2 → mixedEmbedding.mixedSpace F | mixedEmbedding.normAtPlace w (v i) < t} := by
    ext v
    simp only [archBox, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun w => ?_
  exact isOpen_lt ((mixedEmbedding.continuous_normAtPlace w).comp (continuous_apply i))
    continuous_const

private theorem zero_mem_archBox {t : ℝ} (ht : 0 < t) :
    (0 : Fin 2 → mixedEmbedding.mixedSpace F) ∈ archBox F t := by
  intro i w
  rw [Pi.zero_apply, map_zero]
  exact ht

private theorem archBox_one_subset :
    archBox F 1 ⊆ Metric.closedBall (0 : Fin 2 → mixedEmbedding.mixedSpace F) 1 := by
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => (hv i w).le

private theorem volume_archBox_one_pos : 0 < MeasureTheory.volume (archBox F 1) :=
  (isOpen_archBox 1).measure_pos _ ⟨0, zero_mem_archBox one_pos⟩

private theorem volume_archBox_one_lt_top : MeasureTheory.volume (archBox F 1) < ⊤ :=
  (MeasureTheory.measure_mono archBox_one_subset).trans_lt MeasureTheory.measure_closedBall_lt_top

private theorem archBox_eq_smul {t : ℝ} (ht : 0 < t) : archBox F t = t • archBox F 1 := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
  constructor
  · intro hv i w
    have := hv i w
    rw [Pi.smul_apply, mixedEmbedding.normAtPlace_smul, abs_of_pos (inv_pos.mpr ht),
      inv_mul_lt_iff₀ ht, mul_one]
    exact this
  · intro hv i w
    have := hv i w
    rwa [Pi.smul_apply, mixedEmbedding.normAtPlace_smul, abs_of_pos (inv_pos.mpr ht),
      inv_mul_lt_iff₀ ht, mul_one] at this

private theorem volume_archBox {t : ℝ} (ht : 0 < t) :
    MeasureTheory.volume (archBox F t)
      = ENNReal.ofReal (t ^ Module.finrank ℝ (Fin 2 → mixedEmbedding.mixedSpace F))
          * MeasureTheory.volume (archBox F 1) := by
  rw [archBox_eq_smul ht, MeasureTheory.Measure.addHaar_smul_of_nonneg MeasureTheory.volume ht.le]

private def latticeBasis₂ (F : Type) [Field F] [NumberField F] :
    Module.Basis (Σ _ : Fin 2, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ
      (Fin 2 → mixedEmbedding.mixedSpace F) :=
  Pi.basis fun _ => mixedEmbedding.latticeBasis F

private theorem exists_of_mem_span_latticeBasis₂ {v : Fin 2 → mixedEmbedding.mixedSpace F}
    (hv : v ∈ Submodule.span ℤ (Set.range (latticeBasis₂ F))) (i : Fin 2) :
    ∃ a : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F a) = v i := by
  rw [Module.Basis.mem_span_iff_repr_mem] at hv
  have hi : v i ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro k
    have := hv ⟨i, k⟩
    rwa [latticeBasis₂, Pi.basis_repr] at this
  rw [mixedEmbedding.mem_span_latticeBasis] at hi
  exact LinearMap.mem_range.mp hi

private theorem volume_fundamentalDomain_pos :
    0 < MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis₂ F)) :=
  pos_iff_ne_zero.mpr (by apply ZSpan.measure_fundamentalDomain_ne_zero)

private theorem volume_fundamentalDomain_lt_top :
    MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis₂ F)) < ⊤ :=
  (ZSpan.fundamentalDomain_isBounded (latticeBasis₂ F)).measure_lt_top

private theorem exists_ne_zero_mem_span_vecMul_mem_archBox
    (T : (Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin 2 → mixedEmbedding.mixedSpace F))
    {t : ℝ}
    (hlt : MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis₂ F))
        * 2 ^ Module.finrank ℝ (Fin 2 → mixedEmbedding.mixedSpace F)
      < MeasureTheory.volume (T ⁻¹' archBox F t)) :
    ∃ v : Fin 2 → mixedEmbedding.mixedSpace F,
      v ∈ Submodule.span ℤ (Set.range (latticeBasis₂ F)) ∧ v ≠ 0 ∧ T v ∈ archBox F t := by
  have hfund := ZSpan.isAddFundamentalDomain' (latticeBasis₂ F) MeasureTheory.volume
  have : Countable (Submodule.span ℤ (Set.range (latticeBasis₂ F))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (latticeBasis₂ F)))
    infer_instance
  have hsymm : ∀ v ∈ T ⁻¹' archBox F t, -v ∈ T ⁻¹' archBox F t := by
    intro v hv
    rw [Set.mem_preimage, map_neg]
    exact neg_mem_archBox hv
  have hconv : Convex ℝ (T ⁻¹' archBox F t) := (convex_archBox t).linear_preimage T
  obtain ⟨⟨v, hv⟩, hvne, hvmem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hsymm hconv hlt
  refine ⟨v, hv, ?_, hvmem⟩
  intro hv0
  exact hvne (Subtype.ext hv0)

end FloorArch

section FloorArchBound

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

private def mixedMatrix (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F) :=
  (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).map (InfiniteAdeleRing.ringEquiv_mixedSpace F)

omit [NumberField F] in
private theorem det_mixedMatrix (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    (mixedMatrix h).det
      = InfiniteAdeleRing.ringEquiv_mixedSpace F (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
  have := RingHom.map_det
    (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F →+* mixedEmbedding.mixedSpace F)
    (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
  have h__af := this.symm
  simp [mixedMatrix, RingHom.mapMatrix_apply] at h__af
  exact h__af

private theorem prod_norm_det_eq (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    ∏ w : InfinitePlace F,
        ‖((archComponent F w h : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ w.mult
      = mixedEmbedding.norm (mixedMatrix h).det := by
  rw [det_mixedMatrix, mixedEmbedding.norm_apply]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [normAtPlace_ringEquiv_mixedSpace, det_archComponent]

private theorem norm_det_mixedMatrix_pos (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    0 < mixedEmbedding.norm (mixedMatrix h).det := by
  rw [← prod_norm_det_eq]
  refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr ?_) _
  exact (Matrix.isUnits_det_units (archComponent F w h)).ne_zero

private theorem norm_bottom_entry_eq (γ : GL (Fin 2) F) (h : GL (Fin 2) (InfiniteAdeleRing F))
    {v : Fin 2 → mixedEmbedding.mixedSpace F}
    (hv : ∀ j, v j = mixedEmbedding F ((γ : Matrix (Fin 2) (Fin 2) F) 1 j))
    (w : InfinitePlace F) (i : Fin 2) :
    ‖((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 i‖
      = mixedEmbedding.normAtPlace w (Matrix.vecMul v (mixedMatrix h) i) := by
  have hR : Matrix.vecMul v (mixedMatrix h) i
      = InfiniteAdeleRing.ringEquiv_mixedSpace F
          (algebraMap F (InfiniteAdeleRing F) ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)
              * (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 i
            + algebraMap F (InfiniteAdeleRing F) ((γ : Matrix (Fin 2) (Fin 2) F) 1 1)
              * (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 i) := by
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hv, mixedMatrix, Matrix.map_apply,
      InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_add, map_mul]
  rw [hR, normAtPlace_ringEquiv_mixedSpace, map_mul, Units.val_mul, Matrix.mul_apply,
    Fin.sum_univ_two, AutomorphicForm.SiegelReduction.archComponent_globalPoints_apply,
    AutomorphicForm.SiegelReduction.archComponent_globalPoints_apply]
  rfl

private theorem le_localHeight_of_bottom_lt (γ : GL (Fin 2) F) (h : GL (Fin 2) (InfiniteAdeleRing F))
    (w : InfinitePlace F) {t : ℝ}
    (hrow : ∀ i : Fin 2,
      ‖((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) 1 i‖ < t) :
    w (γ : Matrix (Fin 2) (Fin 2) F).det
        * ‖((archComponent F w h : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖
        / (2 * t ^ 2)
      ≤ WindowedSiegel.localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)) := by
  set g := archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) with hg
  have hdet : ‖((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖
      = w (γ : Matrix (Fin 2) (Fin 2) F).det
          * ‖((archComponent F w h : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion).det‖ := by
    rw [hg, map_mul, Units.val_mul, Matrix.det_mul, norm_mul,
      AutomorphicForm.SiegelReduction.det_archComponent_globalPoints,
      AutomorphicForm.SiegelReduction.norm_coe_completion]
  have hrowle : WindowedSiegel.rowNormSq ((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      ≤ 2 * t ^ 2 := by
    unfold WindowedSiegel.rowNormSq
    have h0 := pow_lt_pow_left₀ (hrow 0) (norm_nonneg _) two_ne_zero
    have h1 := pow_lt_pow_left₀ (hrow 1) (norm_nonneg _) two_ne_zero
    linarith
  unfold WindowedSiegel.localHeight
  rw [← hdet]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (WindowedSiegel.rowNormSq_pos g) hrowle

private theorem le_archHeight_of_forall_bottom_lt (γ : GL (Fin 2) F)
    (h : GL (Fin 2) (InfiniteAdeleRing F)) {t : ℝ}
    (hrow : ∀ (w : InfinitePlace F) (i : Fin 2),
      ‖((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) 1 i‖ < t) :
    (∏ w : InfinitePlace F, w (γ : Matrix (Fin 2) (Fin 2) F).det ^ w.mult)
        * mixedEmbedding.norm (mixedMatrix h).det / (2 * t ^ 2) ^ Module.finrank ℚ F
      ≤ archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) := by
  unfold archHeight
  calc (∏ w : InfinitePlace F, w (γ : Matrix (Fin 2) (Fin 2) F).det ^ w.mult)
          * mixedEmbedding.norm (mixedMatrix h).det / (2 * t ^ 2) ^ Module.finrank ℚ F
      = ∏ w : InfinitePlace F,
          (w (γ : Matrix (Fin 2) (Fin 2) F).det
            * ‖((archComponent F w h : GL (Fin 2) w.Completion) :
                Matrix (Fin 2) (Fin 2) w.Completion).det‖ / (2 * t ^ 2)) ^ w.mult := by
        rw [← prod_norm_det_eq, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum,
          ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [div_pow, mul_pow (w (γ : Matrix (Fin 2) (Fin 2) F).det)]
    _ ≤ ∏ w : InfinitePlace F,
          WindowedSiegel.localHeight
            (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)) ^ w.mult := by
        refine Finset.prod_le_prod (fun w _ => pow_nonneg ?_ _) fun w _ => ?_
        · exact div_nonneg (mul_nonneg (apply_nonneg _ _) (norm_nonneg _)) (by positivity)
        · exact pow_le_pow_left₀ (div_nonneg (mul_nonneg (apply_nonneg _ _) (norm_nonneg _))
            (by positivity)) (le_localHeight_of_bottom_lt γ h w (hrow w)) _

private theorem finrank_two_mixedSpace :
    Module.finrank ℝ (Fin 2 → mixedEmbedding.mixedSpace F) = 2 * Module.finrank ℚ F := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    mixedEmbedding.finrank, smul_eq_mul]

private theorem exists_pos_forall_exists_le_archHeight (F : Type) [Field F] [NumberField F] :
    ∃ c : ℝ, 0 < c ∧ ∀ h : GL (Fin 2) (InfiniteAdeleRing F), ∃ γ : GL (Fin 2) F, ∃ p q : 𝓞 F,
      ((γ : Matrix (Fin 2) (Fin 2) F) 1 0 = algebraMap (𝓞 F) F p
        ∧ (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = algebraMap (𝓞 F) F q)
      ∧ c * ∏ w : InfinitePlace F, w (γ : Matrix (Fin 2) (Fin 2) F).det ^ w.mult
          ≤ archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) := by
  classical

  set N : ℕ := Module.finrank ℝ (Fin 2 → mixedEmbedding.mixedSpace F) with hN
  set n : ℕ := Module.finrank ℚ F with hn
  have hN2 : N = 2 * n := finrank_two_mixedSpace
  have hNpos : N ≠ 0 := by
    rw [hN2, hn]
    exact mul_ne_zero two_ne_zero Module.finrank_pos.ne'
  set V₀ : ℝ := (MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis₂ F))).toReal with hV₀
  have hV₀pos : 0 < V₀ :=
    ENNReal.toReal_pos volume_fundamentalDomain_pos.ne' volume_fundamentalDomain_lt_top.ne
  set v₁ : ℝ := (MeasureTheory.volume (archBox F 1)).toReal with hv₁
  have hv₁pos : 0 < v₁ := ENNReal.toReal_pos volume_archBox_one_pos.ne' volume_archBox_one_lt_top.ne
  have hFD : MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis₂ F)) = ENNReal.ofReal V₀ :=
    (ENNReal.ofReal_toReal volume_fundamentalDomain_lt_top.ne).symm
  have hB1 : MeasureTheory.volume (archBox F 1) = ENNReal.ofReal v₁ :=
    (ENNReal.ofReal_toReal volume_archBox_one_lt_top.ne).symm
  refine ⟨v₁ / (2 ^ n * 2 ^ (N + 1) * V₀), by positivity, fun h => ?_⟩

  set M := mixedMatrix h with hM
  set D : ℝ := mixedEmbedding.norm M.det with hD
  have hDpos : 0 < D := norm_det_mixedMatrix_pos h
  set T : (Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin 2 → mixedEmbedding.mixedSpace F) :=
    (Matrix.toLin' M.transpose).restrictScalars ℝ with hT
  have habsT : |LinearMap.det T| = D := abs_det_vecMul M
  have hdetT : LinearMap.det T ≠ 0 := fun h0 => by
    rw [h0, abs_zero] at habsT
    exact hDpos.ne habsT
  have hTapply : ∀ v, T v = Matrix.vecMul v M := fun v => by
    rw [hT, LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_transpose]

  set base : ℝ := 2 ^ (N + 1) * V₀ * D / v₁ with hbase
  have hbasepos : 0 < base := by positivity
  set t : ℝ := base ^ ((N : ℝ)⁻¹) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hbasepos _
  have htN : t ^ N = base := Real.rpow_inv_natCast_pow hbasepos.le hNpos

  have hvol : MeasureTheory.volume (T ⁻¹' archBox F t)
      = ENNReal.ofReal (D⁻¹ * (t ^ N * v₁)) := by
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hdetT, volume_archBox htpos, hB1,
      abs_inv, habsT, ← hN, ← ENNReal.ofReal_mul (pow_nonneg htpos.le N),
      ← ENNReal.ofReal_mul (inv_pos.mpr hDpos).le]
  have hlt : MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis₂ F)) * 2 ^ N
      < MeasureTheory.volume (T ⁻¹' archBox F t) := by
    rw [hvol, hFD, show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
      rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul hV₀pos.le,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos (inv_pos.mpr hDpos) (mul_pos (pow_pos htpos N) hv₁pos)),
      htN, hbase]
    have hkey : D⁻¹ * (2 ^ (N + 1) * V₀ * D / v₁ * v₁) = 2 * (2 ^ N * V₀) := by
      rw [pow_succ]
      field
    rw [hkey]
    linarith [mul_pos (pow_pos two_pos N) hV₀pos]
  obtain ⟨v, hvspan, hvne, hvbox⟩ := exists_ne_zero_mem_span_vecMul_mem_archBox T hlt
  obtain ⟨p, hp⟩ := exists_of_mem_span_latticeBasis₂ hvspan 0
  obtain ⟨q, hq⟩ := exists_of_mem_span_latticeBasis₂ hvspan 1

  have hpq : algebraMap (𝓞 F) F p ≠ 0 ∨ algebraMap (𝓞 F) F q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hvne
    ext i : 1
    fin_cases i
    · simp [← hp, hcon.1]
    · simp [← hq, hcon.2]
  obtain ⟨γ, hγ0, hγ1⟩ := exists_gl_bottom_row _ _ hpq
  refine ⟨γ, p, q, ⟨hγ0, hγ1⟩, ?_⟩
  have hv : ∀ j : Fin 2, v j = mixedEmbedding F ((γ : Matrix (Fin 2) (Fin 2) F) 1 j) := by
    intro j
    fin_cases j
    · simpa [hγ0] using hp.symm
    · simpa [hγ1] using hq.symm
  have hrow : ∀ (w : InfinitePlace F) (i : Fin 2),
      ‖((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) 1 i‖ < t := by
    intro w i
    rw [norm_bottom_entry_eq γ h hv w i]
    have := hvbox i w
    rwa [hTapply] at this
  refine le_trans (le_of_eq ?_) (le_archHeight_of_forall_bottom_lt γ h hrow)

  have ht2 : (2 * t ^ 2) ^ n = 2 ^ n * base := by
    rw [mul_pow, ← pow_mul, ← hN2, htN]
  rw [← hn, ht2, hbase, ← hM, ← hD]
  field

end FloorArchBound

private theorem exists_forall_exists_le_adelicHeight_globalPoints_mul (K : Type) [Field K]
    [NumberField K] :
    ∃ μ : ℝ, 0 < μ ∧ ∀ g : AdelicGL2 (𝓞 K) K, ∃ γ : GL (Fin 2) K,
      μ ≤ adelicHeight K (globalPoints (𝓞 K) K γ * g) := by
  classical
  obtain ⟨R, hR⟩ := exists_finset_forall_exists_upper_mem K
  obtain ⟨c, hc, hfloor⟩ := exists_pos_forall_exists_le_archHeight K
  have hS : 0 < 1 + ∑ a ∈ R, pieceBound a :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun a _ => (pieceBound_pos a).le)
  refine ⟨c / (1 + ∑ a ∈ R, pieceBound a), div_pos hc hS, fun g => ?_⟩

  obtain ⟨a, ha, b, hb, s, hmem⟩ := hR g
  set k := glFin (𝓞 K) K (globalPoints (𝓞 K) K b) * glFin (𝓞 K) K g *
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * (glFin (𝓞 K) K (finIdeleDiag K a))⁻¹ with hk
  have hkeq : glFin (𝓞 K) K (globalPoints (𝓞 K) K b) * glFin (𝓞 K) K g *
      Matrix.GeneralLinearGroup.scalar (Fin 2) s = k * glFin (𝓞 K) K (finIdeleDiag K a) := by
    rw [hk, inv_mul_cancel_right]

  obtain ⟨γ₁, p, q, ⟨hp, hq⟩, harch⟩ :=
    hfloor (glArch (𝓞 K) K (globalPoints (𝓞 K) K b * g))
  refine ⟨γ₁ * b, ?_⟩
  have hdet0 : (γ₁ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnits_det_units γ₁).ne_zero

  have hsplit : globalPoints (𝓞 K) K (γ₁ * b) * g
      = globalPoints (𝓞 K) K γ₁ * (globalPoints (𝓞 K) K b * g) := by
    rw [map_mul, mul_assoc]
  have harch' : c * ∏ w : InfinitePlace K, w (γ₁ : Matrix (Fin 2) (Fin 2) K).det ^ w.mult
      ≤ archHeight K (glArch (𝓞 K) K (globalPoints (𝓞 K) K (γ₁ * b) * g)) := by
    rw [hsplit, map_mul]
    exact harch
  have hfin' : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖FinitePlace.embedding v ((γ₁ : Matrix (Fin 2) (Fin 2) K).det)‖) / pieceBound a
      ≤ finHeight K (glFin (𝓞 K) K (globalPoints (𝓞 K) K (γ₁ * b) * g)) := by
    rw [← finHeight_mul_scalar _ s, hsplit, map_mul, map_mul,
      mul_assoc (glFin (𝓞 K) K (globalPoints (𝓞 K) K γ₁)), hkeq, ← mul_assoc]
    exact finprod_norm_embedding_det_div_le_finHeight hp hq hmem a

  have hprod : (∏ w : InfinitePlace K, w (γ₁ : Matrix (Fin 2) (Fin 2) K).det ^ w.mult)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ‖FinitePlace.embedding v ((γ₁ : Matrix (Fin 2) (Fin 2) K).det)‖ = 1 := by
    rw [finprod_norm_embedding]
    exact NumberField.prod_abs_eq_one hdet0
  have hP : 0 ≤ ∏ w : InfinitePlace K, w (γ₁ : Matrix (Fin 2) (Fin 2) K).det ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg _ _) _
  have hQ : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v ((γ₁ : Matrix (Fin 2) (Fin 2) K).det)‖ :=
    finprod_nonneg fun v => norm_nonneg _
  have hpb : pieceBound a ≤ 1 + ∑ a ∈ R, pieceBound a :=
    le_add_of_nonneg_of_le zero_le_one
      (Finset.single_le_sum (fun a _ => (pieceBound_pos a).le) ha)
  unfold adelicHeight
  calc c / (1 + ∑ a ∈ R, pieceBound a)
      ≤ c / pieceBound a := div_le_div_of_nonneg_left hc.le (pieceBound_pos a) hpb
    _ = (c * ∏ w : InfinitePlace K, w (γ₁ : Matrix (Fin 2) (Fin 2) K).det ^ w.mult)
          * ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
              ‖FinitePlace.embedding v ((γ₁ : Matrix (Fin 2) (Fin 2) K).det)‖) / pieceBound a) := by
        rw [mul_div_assoc', mul_assoc, hprod, mul_one]
    _ ≤ archHeight K (glArch (𝓞 K) K (globalPoints (𝓞 K) K (γ₁ * b) * g))
          * finHeight K (glFin (𝓞 K) K (globalPoints (𝓞 K) K (γ₁ * b) * g)) :=
        mul_le_mul harch' hfin' (div_nonneg hQ (pieceBound_pos a).le)
          ((mul_nonneg hc.le hP).trans harch')

section UnitBalancingFurniture

private theorem exists_forall_abs_mult_mul_log_add_le (K : Type) [Field K] [NumberField K] :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : NumberField.Units.dirichletUnitTheorem.logSpace K, ∃ ε : (𝓞 K)ˣ,
      ∀ w : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
        |(w.1.mult : ℝ) * Real.log (w.1 ((ε : 𝓞 K) : K)) + x w| ≤ D := by
  classical
  let B := (NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), fun x => ?_⟩
  set v : NumberField.Units.dirichletUnitTheorem.logSpace K :=
    (ZSpan.floor B (-x) : NumberField.Units.dirichletUnitTheorem.logSpace K) with hv
  have hvmem : v ∈ NumberField.Units.unitLattice K := by
    have h := (ZSpan.floor B (-x)).2
    rwa [← Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice K)]
  obtain ⟨u, -, hu⟩ := hvmem
  have hu' : NumberField.Units.logEmbedding K u = v := hu
  have hxv : x + v = -(ZSpan.fract B (-x)) := by
    rw [ZSpan.fract_apply, ← hv]
    abel
  have hnorm : ‖x + v‖ ≤ ∑ i, ‖B i‖ := by
    rw [hxv, norm_neg]
    exact ZSpan.norm_fract_le B (-x)
  refine ⟨Additive.toMul u, fun w => ?_⟩
  have hcoord : (w.1.mult : ℝ) * Real.log (w.1 (((Additive.toMul u : (𝓞 K)ˣ) : 𝓞 K) : K)) = v w := by
    rw [← hu']
    exact (NumberField.Units.dirichletUnitTheorem.logEmbedding_component (Additive.toMul u) w).symm
  have hpi : |x w + v w| ≤ ‖x + v‖ := by
    have h := norm_le_pi_norm (x + v) w
    rwa [Pi.add_apply, Real.norm_eq_abs] at h
  rw [hcoord, add_comm]
  exact hpi.trans hnorm

private theorem exists_forall_neg_le_add_mult_mul_log (K : Type) [Field K] [NumberField K] :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : InfinitePlace K → ℝ, ∑ w, x w = 0 → ∃ ε : (𝓞 K)ˣ,
      ∀ w : InfinitePlace K, -D ≤ x w + (w.mult : ℝ) * Real.log (w ((ε : 𝓞 K) : K)) := by
  classical
  obtain ⟨D, hD, hex⟩ := exists_forall_abs_mult_mul_log_add_le K
  refine ⟨D + ∑ _i : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, D,
    add_nonneg hD (Finset.sum_nonneg fun _ _ => hD), fun x hx => ?_⟩
  obtain ⟨ε, hε⟩ := hex (fun w => x w.1)
  refine ⟨ε, fun w => ?_⟩
  set e : InfinitePlace K → ℝ := fun w => x w + (w.mult : ℝ) * Real.log (w ((ε : 𝓞 K) : K)) with he
  have hoff : ∀ w : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      -D ≤ e w.1 ∧ e w.1 ≤ D := fun w => by
    have h : |(w.1.mult : ℝ) * Real.log (w.1 ((ε : 𝓞 K) : K)) + x w.1| ≤ D := hε w
    obtain ⟨h1, h2⟩ := abs_le.mp h
    simp only [he]
    constructor <;> linarith
  have hsum : ∑ w, e w = 0 := by
    simp only [he, Finset.sum_add_distrib, hx, zero_add]
    exact NumberField.Units.sum_mult_mul_log ε
  show -(D + ∑ _i : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, D) ≤ e w
  have hle : ∑ i : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, e i.1 ≤
      ∑ _i : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, D :=
    Finset.sum_le_sum fun i _ => (hoff i).2
  have hsum0 : 0 ≤ ∑ _i : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, D :=
    Finset.sum_nonneg fun _ _ => hD
  by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
  · have key : e NumberField.Units.dirichletUnitTheorem.w₀ +
        ∑ i : {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, e i.1 = 0 :=
      (Fintype.sum_eq_add_sum_subtype_ne e NumberField.Units.dirichletUnitTheorem.w₀).symm.trans hsum
    rw [hw]
    linarith
  · have h : -D ≤ e w := (hoff ⟨w, hw⟩).1
    linarith

private theorem log_le_sum_mult_mul_log {K : Type} [Field K] [NumberField K] {κ : ℝ} (hκ : 0 < κ)
    (t : InfinitePlace K → ℝ) (ht : ∀ w, 0 < t w) (h : κ ≤ ∏ w : InfinitePlace K, t w ^ w.mult) :
    Real.log κ ≤ ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (t w) := by
  calc Real.log κ ≤ Real.log (∏ w : InfinitePlace K, t w ^ w.mult) := Real.log_le_log hκ h
    _ = ∑ w : InfinitePlace K, Real.log (t w ^ w.mult) :=
        Real.log_prod (fun w _ => pow_ne_zero _ (ht w).ne')
    _ = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (t w) := by
        simp only [Real.log_pow]

end UnitBalancingFurniture

private theorem exists_forall_exists_units_le_mul_apply (K : Type) [Field K] [NumberField K]
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : InfinitePlace K → ℝ, (∀ w, 0 < t w) →
      κ ≤ ∏ w : InfinitePlace K, t w ^ w.mult →
        ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K, c ≤ t w * w ((ε : 𝓞 K) : K) := by
  classical
  obtain ⟨D, hD, hbal⟩ := exists_forall_neg_le_add_mult_mul_log K
  have hM : (0 : ℝ) < ∑ w : InfinitePlace K, (w.mult : ℝ) :=
    Finset.sum_pos (fun w _ => zero_lt_one.trans_le (NumberField.InfinitePlace.one_le_mult (w := w)))
      Finset.univ_nonempty
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (∑ w : InfinitePlace K, (w.mult : ℝ)) * b = Real.log κ :=
    ⟨(∑ w : InfinitePlace K, (w.mult : ℝ))⁻¹ * Real.log κ, by
      rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]⟩
  refine ⟨Real.exp (b - D), Real.exp_pos _, fun t ht hprod => ?_⟩
  have hL : Real.log κ ≤ ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (t w) :=
    log_le_sum_mult_mul_log hκ t ht hprod
  obtain ⟨a, ha⟩ : ∃ a : ℝ, (∑ w : InfinitePlace K, (w.mult : ℝ)) * a =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (t w) :=
    ⟨(∑ w : InfinitePlace K, (w.mult : ℝ))⁻¹ * ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (t w), by
      rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]⟩
  have hba : b ≤ a := by
    rcases le_or_gt b a with h | h
    · exact h
    · exfalso
      have h' := mul_lt_mul_of_pos_left h hM
      linarith
  have hsum0 : ∑ w : InfinitePlace K, ((w.mult : ℝ) * Real.log (t w) - (w.mult : ℝ) * a) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    linarith
  obtain ⟨ε, hε⟩ := hbal (fun w => (w.mult : ℝ) * Real.log (t w) - (w.mult : ℝ) * a) hsum0
  refine ⟨ε, fun w => ?_⟩
  have hε0 : ((ε : 𝓞 K) : K) ≠ 0 := NumberField.Units.coe_ne_zero ε
  have hwε : 0 < w ((ε : 𝓞 K) : K) := NumberField.InfinitePlace.pos_iff.mpr hε0
  have h1 : -D ≤ ((w.mult : ℝ) * Real.log (t w) - (w.mult : ℝ) * a) +
      (w.mult : ℝ) * Real.log (w ((ε : 𝓞 K) : K)) := hε w
  have hm1 : (1 : ℝ) ≤ (w.mult : ℝ) := NumberField.InfinitePlace.one_le_mult
  have hab' : (w.mult : ℝ) * b ≤ (w.mult : ℝ) * a :=
    mul_le_mul_of_nonneg_left hba (zero_le_one.trans hm1)
  have hDm : D ≤ (w.mult : ℝ) * D := le_mul_of_one_le_left hD hm1
  have hkey : b - D ≤ Real.log (t w) + Real.log (w ((ε : 𝓞 K) : K)) := by
    rcases le_or_gt (b - D) (Real.log (t w) + Real.log (w ((ε : 𝓞 K) : K))) with h | h
    · exact h
    · exfalso
      have hpos : 0 ≤ b - Real.log (t w) - Real.log (w ((ε : 𝓞 K) : K)) - D := by linarith
      have hprod' := le_mul_of_one_le_left hpos hm1
      linarith
  calc Real.exp (b - D) ≤ Real.exp (Real.log (t w * w ((ε : 𝓞 K) : K))) := by
        rw [Real.log_mul (ht w).ne' hwε.ne']
        exact Real.exp_le_exp.mpr hkey
    _ = t w * w ((ε : 𝓞 K) : K) := Real.exp_log (mul_pos (ht w) hwε)

variable (K : Type) [Field K] in

private def unipGlobal (t : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by simp [Matrix.det_fin_two_of])

private theorem xwin_archComponent_globalPoints (K : Type) [Field K] [NumberField K]
    (M : GL (Fin 2) K) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (globalPoints (𝓞 K) K M))
      = Matrix.GeneralLinearGroup.map (algebraMap K w.Completion) M := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rfl

private theorem xwin_xWindowSq_unip_mul {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (u m : GL (Fin 2) w.Completion)
    (h00 : (u : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = 1)
    (h10 : (u : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0)
    (h11 : (u : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = 1) :
    xWindowSq (u * m)
      = ‖xCoord ((m : Matrix (Fin 2) (Fin 2) w.Completion).map
            (InfinitePlace.Completion.extensionEmbedding w))
          + InfinitePlace.Completion.extensionEmbedding w
              ((u : Matrix (Fin 2) (Fin 2) w.Completion) 0 1)‖ ^ 2 := by
  rw [SiegelCoordinates.xWindowSq_eq_norm_xCoord_map_sq (InfinitePlace.Completion.extensionEmbedding w)
    (SiegelCoordinates.norm_extensionEmbedding w) (u * m)]
  have hcoe : ((u * m : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map
        (InfinitePlace.Completion.extensionEmbedding w)
      = ((Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbedding w) u
          * Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbedding w) m :
            GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← map_mul]
    rfl
  have e00 : ((Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbedding w) u :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by
    rw [SiegelCoordinates.coe_map, Matrix.map_apply, h00, map_one]
  have e01 : ((Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbedding w) u :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        = InfinitePlace.Completion.extensionEmbedding w
            ((u : Matrix (Fin 2) (Fin 2) w.Completion) 0 1) := by
    rw [SiegelCoordinates.coe_map, Matrix.map_apply]
  have e10 : ((Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbedding w) u :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    rw [SiegelCoordinates.coe_map, Matrix.map_apply, h10, map_zero]
  have e11 : ((Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbedding w) u :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by
    rw [SiegelCoordinates.coe_map, Matrix.map_apply, h11, map_one]
  rw [hcoe, SiegelCoordinates.xCoord_upper_entries_mul one_ne_zero e00 e01 e10 e11,
    SiegelCoordinates.coe_map]
  simp only [div_one, one_mul]

private theorem xwin_exists_extensionEmbedding_eq_xCoord {K : Type} [Field K] [NumberField K]
    (w : InfinitePlace K) (m : GL (Fin 2) w.Completion) :
    ∃ x : w.Completion, InfinitePlace.Completion.extensionEmbedding w x
      = xCoord ((m : Matrix (Fin 2) (Fin 2) w.Completion).map
          (InfinitePlace.Completion.extensionEmbedding w)) := by
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin 2) (Fin 2) ℝ,
        R = (m : Matrix (Fin 2) (Fin 2) w.Completion).map
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) := ⟨_, rfl⟩
    have hmap : (m : Matrix (Fin 2) (Fin 2) w.Completion).map
          (InfinitePlace.Completion.extensionEmbedding w)
        = R.map (fun s : ℝ => (s : ℂ)) := by
      ext i j
      simp only [hR, Matrix.map_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      ((R 0 0 * R 1 0 + R 0 1 * R 1 1) / rowNormSq (R.map (fun s : ℝ => (s : ℂ)))), ?_⟩
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply, hmap]
    simp only [xCoord, Matrix.map_apply, Complex.conj_ofReal]
    push_cast
    ring
  · refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
      (xCoord ((m : Matrix (Fin 2) (Fin 2) w.Completion).map
        (InfinitePlace.Completion.extensionEmbedding w))), ?_⟩
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hw, RingEquiv.apply_symm_apply]

private theorem exists_forall_exists_xWindowSq_unipGlobal_mul_le (K : Type) [Field K]
    [NumberField K] :
    ∃ r : ℝ, ∀ g : AdelicGL2 (𝓞 K) K, ∃ o : 𝓞 K, ∀ w : InfinitePlace K,
      xWindowSq (archComponent K w (glArch (𝓞 K) K
        (globalPoints (𝓞 K) K (unipGlobal K (o : K)) * g))) ≤ r ^ 2 := by
  obtain ⟨r, hr⟩ := NumberField.AdelicBox.exists_forall_norm_apply_le_of_mem_infiniteBox K
  refine ⟨r, fun g => ?_⟩
  choose x hx using fun w : InfinitePlace K =>
    xwin_exists_extensionEmbedding_eq_xCoord w (archComponent K w (glArch (𝓞 K) K g))
  obtain ⟨o, ho⟩ := (NumberField.AdelicBox.existsUnique_int_add_mem_infiniteBox K x).exists
  refine ⟨o, fun w => ?_⟩
  rw [map_mul, map_mul, xwin_archComponent_globalPoints K (unipGlobal K (o : K)) w,
    xwin_xWindowSq_unip_mul _ _ ?_ ?_ ?_]
  · have hentry : ((Matrix.GeneralLinearGroup.map (algebraMap K w.Completion) (unipGlobal K (o : K)) :
          GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 1
        = algebraMap K w.Completion (o : K) := rfl
    have hbox : ‖algebraMap K w.Completion (o : K) + x w‖ ≤ r := hr _ ho w
    rw [← hx w, hentry, ← map_add, SiegelCoordinates.norm_extensionEmbedding, add_comm]
    exact pow_le_pow_left₀ (norm_nonneg _) hbox 2
  · show algebraMap K w.Completion 1 = 1
    exact map_one _
  · show algebraMap K w.Completion 0 = 0
    exact map_zero _
  · show algebraMap K w.Completion 1 = 1
    exact map_one _

section Normalise

variable {F : Type} [Field F] [NumberField F]

private theorem cover_archDetNorm_mul (w : InfinitePlace F) (g h : AdelicGL2 (𝓞 F) F) :
    AdelicVolume.archDetNorm w (g * h)
      = AdelicVolume.archDetNorm w g * AdelicVolume.archDetNorm w h := by
  unfold AdelicVolume.archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private theorem cover_archDetNorm_centralScalar (v : InfinitePlace F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    AdelicVolume.archDetNorm v (centralScalar (𝓞 F) F z)
      = ‖(z : AdeleRing (𝓞 F) F).1 v‖ * ‖(z : AdeleRing (𝓞 F) F).1 v‖ := by
  unfold AdelicVolume.archDetNorm
  set s := archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then (z : AdeleRing (𝓞 F) F).1 v else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [AdelicVolume.centralScalar_apply_eq, if_pos rfl]
    · rw [AdelicVolume.centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

private theorem cover_archDetNorm_centralScalar_mul (v : InfinitePlace F) (z : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    AdelicVolume.archDetNorm v (centralScalar (𝓞 F) F z * g)
      = (‖(z : AdeleRing (𝓞 F) F).1 v‖ * ‖(z : AdeleRing (𝓞 F) F).1 v‖)
          * AdelicVolume.archDetNorm v g := by
  rw [cover_archDetNorm_mul, cover_archDetNorm_centralScalar]

omit [NumberField F] in

private theorem cover_exists_norm_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 < r) :
    ∃ a : v.Completion, a ≠ 0 ∧ ‖a‖ = r := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r, ?_, ?_⟩
    · rw [ne_eq, ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm,
        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.injective.eq_iff]
      exact hr.ne'
    · have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _) ((InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r)
      rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv, RingEquiv.apply_symm_apply,
        Real.norm_eq_abs, abs_of_pos hr] at h
      exact h.symm
  · refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (r : ℂ), ?_, ?_⟩
    · rw [ne_eq, ← map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm,
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.injective.eq_iff,
        Complex.ofReal_eq_zero]
      exact hr.ne'
    · have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (r : ℂ))
      rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv, RingEquiv.apply_symm_apply,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
      exact h.symm

omit [NumberField F] in
private theorem cover_exists_norm_mul_self_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 < r) :
    ∃ a : v.Completion, a ≠ 0 ∧ ‖a‖ * ‖a‖ = r := by
  obtain ⟨a, ha0, ha⟩ := cover_exists_norm_eq v (Real.sqrt_pos.mpr hr)
  exact ⟨a, ha0, by rw [ha, Real.mul_self_sqrt hr.le]⟩

variable (F) in

private def cover_archIdele (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (fun v => (a v : v.Completion), 1)
  inv := (fun v => ((a v)⁻¹ : (v.Completion)ˣ), 1)
  val_inv := Prod.ext (funext fun v => Units.mul_inv (a v)) (one_mul 1)
  inv_val := Prod.ext (funext fun v => Units.inv_mul (a v)) (one_mul 1)

private theorem cover_archIdele_fst (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) (v : InfinitePlace F) :
    ((cover_archIdele F a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = a v := rfl

private theorem cover_archIdele_snd (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) :
    ((cover_archIdele F a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

private theorem cover_glFin_centralScalar_of_snd_eq_one {z : (AdeleRing (𝓞 F) F)ˣ}
    (hz : (z : AdeleRing (𝓞 F) F).2 = 1) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 :=
  glFin_scalar_eq_one F hz (AdelicVolume.centralScalar_apply_eq z 0)
    (AdelicVolume.centralScalar_apply_ne z (by decide)) (AdelicVolume.centralScalar_apply_ne z (by decide))
    (AdelicVolume.centralScalar_apply_eq z 1)

private theorem cover_centralScalar_mul_mem {c u d₁ d₂ : ℝ} {z : (AdeleRing (𝓞 F) F)ˣ}
    (hzK : glFin (𝓞 F) F (centralScalar (𝓞 F) F z) ∈ finiteIntegralGL2 (𝓞 F) F)
    (hza : ∀ v : InfinitePlace F, (z : AdeleRing (𝓞 F) F).1 v ≠ 0) {h : AdelicGL2 (𝓞 F) F}
    (hK : glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F)
    (hfloor : ∀ v : InfinitePlace F, c ≤ localHeight (archComponent F v (glArch (𝓞 F) F h)))
    (hwin : ∀ v : InfinitePlace F, xWindowSq (archComponent F v (glArch (𝓞 F) F h)) ≤ u ^ 2)
    (hdet : ∀ v : InfinitePlace F,
      AdelicVolume.archDetNorm v (centralScalar (𝓞 F) F z * h) ∈ Set.Icc d₁ d₂) :
    centralScalar (𝓞 F) F z * h ∈ centreCutSiegelSet F c u d₁ d₂ := by
  have hdiag : ∀ (v : InfinitePlace F) (i : Fin 2),
      ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i i = (z : AdeleRing (𝓞 F) F).1 v := by
    intro v i
    simp only [archComponent_apply, glArch_apply]
    rw [AdelicVolume.centralScalar_apply_eq]
  have hoff : ∀ (v : InfinitePlace F) (i j : Fin 2), i ≠ j →
      ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i j = 0 := by
    intro v i j hij
    simp only [archComponent_apply, glArch_apply]
    rw [AdelicVolume.centralScalar_apply_ne _ hij]
    rfl
  refine ⟨?_, fun v => ?_, fun v => ?_, hdet⟩
  · rw [map_mul]
    exact Subgroup.mul_mem _ hzK hK
  · have h00 := hdiag v 0
    have h11 := hdiag v 1
    have h01 := hoff v 0 1 (by decide)
    have h10 := hoff v 1 0 (by decide)
    rw [map_mul, map_mul, localHeight_scalar_entries_mul (hza v) h00 h01 h10 h11]
    exact hfloor v
  · have h00 := hdiag v 0
    have h11 := hdiag v 1
    have h01 := hoff v 0 1 (by decide)
    have h10 := hoff v 1 0 (by decide)
    rw [map_mul, map_mul, xWindowSq_scalar_entries_mul (hza v) h00 h01 h10 h11]
    exact hwin v

private theorem cover_exists_centralScalar_mul_mem {c u d₁ d₂ : ℝ} (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂)
    {h : AdelicGL2 (𝓞 F) F} (hK : glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F)
    (hfloor : ∀ v : InfinitePlace F, c ≤ localHeight (archComponent F v (glArch (𝓞 F) F h)))
    (hwin : ∀ v : InfinitePlace F, xWindowSq (archComponent F v (glArch (𝓞 F) F h)) ≤ u ^ 2) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ, centralScalar (𝓞 F) F z * h ∈ centreCutSiegelSet F c u d₁ d₂ := by
  have hratio : ∀ v : InfinitePlace F, 0 < d₂ / AdelicVolume.archDetNorm v h := fun v =>
    div_pos hd₂ (AdelicVolume.archDetNorm_pos v h)
  choose t ht0 ht using fun v : InfinitePlace F => cover_exists_norm_mul_self_eq v (hratio v)
  set z : (AdeleRing (𝓞 F) F)ˣ := cover_archIdele F fun v => Units.mk0 (t v) (ht0 v) with hz
  have hdet : ∀ v : InfinitePlace F,
      AdelicVolume.archDetNorm v (centralScalar (𝓞 F) F z * h) = d₂ := by
    intro v
    rw [cover_archDetNorm_centralScalar_mul, hz, cover_archIdele_fst, Units.val_mk0, ht v,
      div_mul_cancel₀ _ (AdelicVolume.archDetNorm_pos v h).ne']
  have hz2 : (z : AdeleRing (𝓞 F) F).2 = 1 := by rw [hz]; exact cover_archIdele_snd _
  refine ⟨z, cover_centralScalar_mul_mem ?_ (fun v => ?_) hK hfloor hwin (fun v => ?_)⟩
  · rw [cover_glFin_centralScalar_of_snd_eq_one hz2]
    exact Subgroup.one_mem _
  · rw [hz, cover_archIdele_fst, Units.val_mk0]
    exact ht0 v
  · rw [hdet v]
    exact ⟨hd, le_rfl⟩

end Normalise

section Covering

variable {F : Type} [Field F] [NumberField F]

private def cover_finIdele (s : (FiniteAdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (1, (s : FiniteAdeleRing (𝓞 F) F))
  inv := (1, ((s⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  val_inv := Prod.ext (one_mul 1) (Units.mul_inv s)
  inv_val := Prod.ext (one_mul 1) (Units.inv_mul s)

private theorem cover_glFin_centralScalar_finIdele (s : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F (cover_finIdele s))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        = Matrix.scalar (Fin 2) (s : FiniteAdeleRing (𝓞 F) F) := rfl
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, hsc, Matrix.scalar_apply]
  by_cases h : i = j
  · subst h
    rw [AdelicVolume.centralScalar_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [AdelicVolume.centralScalar_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
    rfl

private theorem cover_glArch_centralScalar_finIdele (s : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    glArch (𝓞 F) F (centralScalar (𝓞 F) F (cover_finIdele s)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply]
  by_cases h : i = j
  · subst h
    rw [AdelicVolume.centralScalar_apply_eq, Units.val_one, Matrix.one_apply_eq]
    rfl
  · rw [AdelicVolume.centralScalar_apply_ne _ h, Units.val_one, Matrix.one_apply_ne h]
    rfl

private def cover_unitDiag (ε : (𝓞 F)ˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![((ε : 𝓞 F) : F), 0; 0, 1] (by
    rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, ne_eq, RingOfIntegers.coe_eq_zero_iff]
    exact ε.ne_zero)

omit [NumberField F] in
private theorem cover_unitDiag_coe (ε : (𝓞 F)ˣ) :
    ((cover_unitDiag ε : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![((ε : 𝓞 F) : F), 0; 0, 1] := rfl

omit [NumberField F] in
private theorem cover_unipGlobal_coe (t : F) :
    ((unipGlobal F t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

omit [NumberField F] in
private theorem cover_unitDiag_mul_unitDiag_inv (ε : (𝓞 F)ˣ) :
    cover_unitDiag ε * cover_unitDiag ε⁻¹ = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, cover_unitDiag_coe, cover_unitDiag_coe, Matrix.mul_fin_two, ← map_mul,
    Units.mul_inv, map_one]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField F] in
private theorem cover_unipGlobal_mul_unipGlobal_neg (t : F) :
    unipGlobal F t * unipGlobal F (-t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, cover_unipGlobal_coe, cover_unipGlobal_coe, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem cover_coe_mem_integralFiniteAdeles (o : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (o : F) ∈ integralFiniteAdeles (𝓞 F) F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one o

private theorem cover_glFin_globalPoints_mem {γ γ' : GL (Fin 2) F} (hγ : γ * γ' = 1)
    (h : ∀ i j, ∃ o : 𝓞 F, (γ : Matrix (Fin 2) (Fin 2) F) i j = o)
    (h' : ∀ i j, ∃ o : 𝓞 F, (γ' : Matrix (Fin 2) (Fin 2) F) i j = o) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) ∈ finiteIntegralGL2 (𝓞 F) F := by
  have hinv : γ⁻¹ = γ' := inv_eq_of_mul_eq_one_right hγ
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨o, ho⟩ := h i j
    rw [glFin_globalPoints_apply, ho]
    exact cover_coe_mem_integralFiniteAdeles o
  · obtain ⟨o, ho⟩ := h' i j
    rw [← map_inv, ← map_inv, hinv, glFin_globalPoints_apply, ho]
    exact cover_coe_mem_integralFiniteAdeles o

private theorem cover_glFin_unitDiag_mem (ε : (𝓞 F)ˣ) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (cover_unitDiag ε)) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine cover_glFin_globalPoints_mem (cover_unitDiag_mul_unitDiag_inv ε) (fun i j => ?_) (fun i j => ?_)
  · rw [cover_unitDiag_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨ε, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rw [cover_unitDiag_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F), rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

private theorem cover_glFin_unipGlobal_mem (o : 𝓞 F) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (unipGlobal F (o : F))) ∈ finiteIntegralGL2 (𝓞 F) F := by
  refine cover_glFin_globalPoints_mem (cover_unipGlobal_mul_unipGlobal_neg (o : F)) (fun i j => ?_)
    (fun i j => ?_)
  · rw [cover_unipGlobal_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨o, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rw [cover_unipGlobal_coe]
    fin_cases i <;> fin_cases j
    · exact ⟨1, by simp⟩
    · exact ⟨-o, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

private theorem cover_localHeight_unitDiag_mul (ε : (𝓞 F)ˣ) (g : AdelicGL2 (𝓞 F) F)
    (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (cover_unitDiag ε) * g)))
      = w ((ε : 𝓞 F) : F) * localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  have h00 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (cover_unitDiag ε))) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0
        = (((ε : 𝓞 F) : F) : w.Completion) := by
    rw [archComponent_globalPoints_apply, cover_unitDiag_coe]
    rfl
  have h10 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (cover_unitDiag ε))) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [archComponent_globalPoints_apply, cover_unitDiag_coe]
    simp; try rfl
  have h11 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (cover_unitDiag ε))) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1
        = ((1 : F) : w.Completion) := by
    rw [archComponent_globalPoints_apply, cover_unitDiag_coe]
    rfl
  have h1 : ((1 : F) : w.Completion) ≠ 0 := by
    rw [← norm_pos_iff, norm_coe_completion, map_one]
    exact one_pos
  rw [map_mul, map_mul, localHeight_upper_entries_mul h1 h00 h10 h11, norm_coe_completion,
    norm_coe_completion, map_one, div_one]

private theorem cover_localHeight_unipGlobal_mul (t : F) (g : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (unipGlobal F t) * g)))
      = localHeight (archComponent F w (glArch (𝓞 F) F g)) := by
  have h00 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (unipGlobal F t))) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0
        = ((1 : F) : w.Completion) := by
    rw [archComponent_globalPoints_apply, cover_unipGlobal_coe]
    rfl
  have h10 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (unipGlobal F t))) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    rw [archComponent_globalPoints_apply, cover_unipGlobal_coe]
    simp; try rfl
  have h11 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (unipGlobal F t))) :
      GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1
        = ((1 : F) : w.Completion) := by
    rw [archComponent_globalPoints_apply, cover_unipGlobal_coe]
    rfl
  have h1 : ((1 : F) : w.Completion) ≠ 0 := by
    rw [← norm_pos_iff, norm_coe_completion, map_one]
    exact one_pos
  rw [map_mul, map_mul, localHeight_upper_entries_mul h1 h00 h10 h11, norm_coe_completion, map_one,
    div_one, one_mul]

private theorem cover_archComponent_finite_moves (X : AdelicGL2 (𝓞 F) F)
    (s a : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    archComponent F w (glArch (𝓞 F) F
        (X * centralScalar (𝓞 F) F (cover_finIdele s) * (finIdeleDiag F a)⁻¹))
      = archComponent F w (glArch (𝓞 F) F X) := by
  simp only [map_mul, map_inv, cover_glArch_centralScalar_finIdele, glArch_finIdeleDiag,
    inv_one, mul_one]

private theorem cover_main (F : Type) [Field F] [NumberField F] :
    ∃ T : Finset (AdelicGL2 (𝓞 F) F), ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ, ∀ d₁ d₂ : ℝ, 0 < d₂ → d₁ ≤ d₂ →
      SiegelCovering.CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  classical

  obtain ⟨μ, hμ, hfloor⟩ := exists_forall_exists_le_adelicHeight_globalPoints_mul F
  obtain ⟨R, hR⟩ := exists_finset_forall_exists_upper_mem F
  set M : ℝ := 1 + ∑ a ∈ R, pieceBound a with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun a _ => (pieceBound_pos a).le)
  have hpiece : ∀ a ∈ R, pieceBound a ≤ M := by
    intro a ha
    rw [hM]
    calc pieceBound a ≤ ∑ a ∈ R, pieceBound a :=
          Finset.single_le_sum (fun a _ => (pieceBound_pos a).le) ha
      _ ≤ 1 + ∑ a ∈ R, pieceBound a := le_add_of_nonneg_left zero_le_one
  obtain ⟨c, hc, hbal⟩ := exists_forall_exists_units_le_mul_apply F (div_pos hμ hM0)
  obtain ⟨r, hwin⟩ := exists_forall_exists_xWindowSq_unipGlobal_mul_le F
  refine ⟨R.image (finIdeleDiag F), c, hc, r, fun d₁ d₂ hd₂ hd g => ?_⟩

  obtain ⟨γ₁, hγ₁⟩ := hfloor g
  set g₁ : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F γ₁ * g with hg₁

  obtain ⟨a, haR, b, hb, s, hmem⟩ := hR g₁
  set g₂ : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F b * g₁ with hg₂
  have hred : μ / M ≤ archHeight F (glArch (𝓞 F) F g₂) := by
    have h₁ := adelicHeight_le_pieceBound_mul_archHeight hb hmem
    rw [← hg₂] at h₁
    have h₂ : μ ≤ pieceBound a * archHeight F (glArch (𝓞 F) F g₂) := hγ₁.trans h₁
    rw [div_le_iff₀ hM0]
    calc μ ≤ pieceBound a * archHeight F (glArch (𝓞 F) F g₂) := h₂
      _ ≤ M * archHeight F (glArch (𝓞 F) F g₂) :=
          mul_le_mul_of_nonneg_right (hpiece a haR) (archHeight_pos F _).le
      _ = archHeight F (glArch (𝓞 F) F g₂) * M := mul_comm _ _

  obtain ⟨ε, hε⟩ := hbal (fun w => localHeight (archComponent F w (glArch (𝓞 F) F g₂)))
    (fun w => localHeight_pos _) hred
  set g₃ : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F (cover_unitDiag ε) * g₂ with hg₃
  have hfloor₃ : ∀ w : InfinitePlace F, c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g₃)) := by
    intro w
    rw [hg₃, cover_localHeight_unitDiag_mul, mul_comm]
    exact hε w

  obtain ⟨o, ho⟩ := hwin g₃
  set g₄ : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F (unipGlobal F (o : F)) * g₃ with hg₄
  have hfloor₄ : ∀ w : InfinitePlace F, c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g₄)) := by
    intro w
    rw [hg₄, cover_localHeight_unipGlobal_mul]
    exact hfloor₃ w
  have hwin₄ : ∀ w : InfinitePlace F, xWindowSq (archComponent F w (glArch (𝓞 F) F g₄)) ≤ r ^ 2 :=
    ho

  set γ : GL (Fin 2) F := unipGlobal F (o : F) * cover_unitDiag ε * b * γ₁ with hγ
  have hγg : globalPoints (𝓞 F) F γ * g = g₄ := by
    rw [hγ, hg₄, hg₃, hg₂, hg₁, map_mul, map_mul, map_mul]
    simp only [mul_assoc]
  set h₀ : AdelicGL2 (𝓞 F) F :=
    g₄ * centralScalar (𝓞 F) F (cover_finIdele s) * (finIdeleDiag F a)⁻¹ with hh₀
  have hK₀ : glFin (𝓞 F) F h₀ ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [hh₀, map_mul, map_mul, map_inv, cover_glFin_centralScalar_finIdele, hg₄, hg₃, map_mul, map_mul]
    have hmem' : glFin (𝓞 F) F (globalPoints (𝓞 F) F b) * glFin (𝓞 F) F g₁ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (glFin (𝓞 F) F (finIdeleDiag F a))⁻¹
          ∈ finiteIntegralGL2 (𝓞 F) F := hmem
    rw [hg₂, map_mul]
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (cover_glFin_unipGlobal_mem o)
      (cover_glFin_unitDiag_mem ε)) hmem'
    convert this using 1
    simp only [mul_assoc]
  have hfloor₀ : ∀ w : InfinitePlace F, c ≤ localHeight (archComponent F w (glArch (𝓞 F) F h₀)) := by
    intro w
    rw [hh₀, cover_archComponent_finite_moves]
    exact hfloor₄ w
  have hwin₀ : ∀ w : InfinitePlace F, xWindowSq (archComponent F w (glArch (𝓞 F) F h₀)) ≤ r ^ 2 := by
    intro w
    rw [hh₀, cover_archComponent_finite_moves]
    exact hwin₄ w

  obtain ⟨z, hz⟩ := cover_exists_centralScalar_mul_mem hd₂ hd hK₀ hfloor₀ hwin₀

  refine ⟨γ, z * cover_finIdele s, ?_⟩
  rw [Set.mem_iUnion₂]
  refine ⟨finIdeleDiag F a, Finset.mem_image_of_mem _ haR, centralScalar (𝓞 F) F z * h₀, hz, ?_⟩
  show centralScalar (𝓞 F) F z * h₀ * finIdeleDiag F a
    = globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F (z * cover_finIdele s)
  rw [hγg, map_mul, hh₀, mul_assoc (centralScalar (𝓞 F) F z), inv_mul_cancel_right,
    ← mul_assoc (centralScalar (𝓞 F) F z) g₄, ← mul_assoc g₄, SiegelCovering.mul_centralScalar_comm z g₄]

end Covering

end SiegelCoveringGeneral
p2m_reactivate "P2MW.S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet.SiegelCoveringGeneral"

end
p2m_reactivate "P2MW.S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet.SiegelCoveringGeneral"

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ T : Finset (AutomorphicForm.AdelicGL2 (𝓞 K) K), ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ,
      ∀ d₁ d₂ : ℝ, 0 < d₂ → d₁ ≤ d₂ →
        AutomorphicForm.SiegelCovering.CoversModCentre K
          (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet K c u d₁ d₂) := by
  exact SiegelCoveringGeneral.cover_main K

end S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
end P2MW
export P2MW.S_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet (solution)
