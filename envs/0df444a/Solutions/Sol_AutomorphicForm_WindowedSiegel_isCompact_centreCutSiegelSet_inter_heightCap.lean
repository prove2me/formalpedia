-- Prove2me | solution 1 for AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f76208ec-475d-59b5-8e8e-e63276efb4fc

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap

open MeasureTheory Set IsDedekindDomain NumberField Metric Matrix

noncomputable section

namespace M4aP1R
namespace BoxedBlock

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre

section GenericBox

variable {K : Type*} [NormedField K]

theorem topNormSq_le_of_box {g : GL (Fin 2) K} {c u d₂ C : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g) (hcap : localHeight g ≤ C)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ≤ d₂) :
    topNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ / c * (u ^ 2 + C ^ 2) := by
  have hrow := rowNormSq_pos g
  have hrowle := rowNormSq_le_of_clauses hc hlh hdet

  have htop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * (xWindowSq g + localHeight g ^ 2) := by
    unfold xWindowSq
    field_simp
    ring
  rw [htop]
  have hlh0 : 0 ≤ localHeight g := le_trans hc.le hlh
  have hxlh : xWindowSq g + localHeight g ^ 2 ≤ u ^ 2 + C ^ 2 := by
    have : localHeight g ^ 2 ≤ C ^ 2 := by nlinarith [hlh0, hcap]
    linarith
  have hxlh0 : 0 ≤ xWindowSq g + localHeight g ^ 2 := by
    have h1 : 0 ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
      unfold topNormSq; positivity
    nlinarith [htop, hrow]
  have hd20 : 0 ≤ d₂ / c := hrow.le.trans hrowle
  exact mul_le_mul hrowle hxlh hxlh0 hd20

theorem entry_norm_le_of_box {g : GL (Fin 2) K} {c u d₁ d₂ C : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g) (hcap : localHeight g ≤ C)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂) (i j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) := by
  have hrowle := rowNormSq_le_of_clauses hc hlh hdet.2
  have htople := topNormSq_le_of_box hc hlh hcap hxw hdet.2
  have hd₂0 : 0 ≤ d₂ / c := div_nonneg (le_trans (norm_nonneg _) hdet.2) hc.le
  have h00 : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖ ^ 2
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖]
  have h01 : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ^ 2
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖]
  have h10 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖]
  have h11 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖]
  have hsplit : d₂ / c * (1 + u ^ 2 + C ^ 2)
      = d₂ / c + d₂ / c * (u ^ 2 + C ^ 2) := by ring
  have hterm : 0 ≤ d₂ / c * (u ^ 2 + C ^ 2) :=
    mul_nonneg hd₂0 (by positivity)
  have hRtop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ d₂ / c * (1 + u ^ 2 + C ^ 2) := by
    rw [hsplit]
    linarith
  have hRrow : rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ d₂ / c * (1 + u ^ 2 + C ^ 2) := by
    rw [hsplit]
    linarith
  refine Real.le_sqrt_of_sq_le ?_
  fin_cases i <;> fin_cases j
  · exact h00.trans hRtop
  · exact h01.trans hRtop
  · exact h10.trans hRrow
  · exact h11.trans hRrow

theorem inv_entry_norm_le_of_box {g : GL (Fin 2) K} {c u d₁ d₂ C : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) (hlh : c ≤ localHeight g) (hcap : localHeight g ≤ C)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) / d₁ := by
  have hB := entry_norm_le_of_box hc hlh hcap hxw hdet
  have hdet0 : ((g : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact absurd hdet.1 (not_le.mpr hd₁)

  have hcoe : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((g : Matrix (Fin 2) (Fin 2) K))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]
  have hadj : ‖((g : Matrix (Fin 2) (Fin 2) K)).adjugate i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) := by
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · show ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ _
      exact hB 1 1
    · show ‖-(g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ≤ _
      rw [norm_neg]; exact hB 0 1
    · show ‖-(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ _
      rw [norm_neg]; exact hB 1 0
    · show ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≤ _
      exact hB 0 0
  have hdinv : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ ≤ d₁⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hd₁ hdet.1
  have h0 : (0 : ℝ) ≤ ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ := by positivity
  calc ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ * ‖((g : Matrix (Fin 2) (Fin 2) K)).adjugate i j‖
      ≤ d₁⁻¹ * Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) := by
        exact mul_le_mul hdinv hadj (norm_nonneg _) (by positivity)
    _ = Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) / d₁ := by
        ring

theorem isCompact_glBox [ProperSpace K] {c u d₁ d₂ C : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) :
    IsCompact {g : GL (Fin 2) K |
      (c ≤ localHeight g ∧ localHeight g ≤ C) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂} := by
  set B := Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) with hB_def
  set S : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      closedBall (0 : K) B with hS_def
  set S' : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      closedBall (0 : K) (B / d₁) with hS'_def
  have hS : IsCompact S :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hS' : IsCompact S' :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) K)) ⁻¹'
      (S ×ˢ (MulOpposite.op '' S'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hS.prod (hS'.image MulOpposite.continuous_op))
  have hclosed : IsClosed {g : GL (Fin 2) K |
      (c ≤ localHeight g ∧ localHeight g ≤ C) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂} := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)
    · exact isClosed_le continuous_const continuous_localHeight
    · exact isClosed_le continuous_localHeight continuous_const
    · exact isClosed_le continuous_xWindowSq continuous_const
    · exact (isClosed_Icc).preimage continuous_det_gl.norm
  refine hK.of_isClosed_subset hclosed ?_
  rintro g ⟨⟨hlh, hcap⟩, hxw, hdet⟩
  have hent := entry_norm_le_of_box hc hlh hcap hxw hdet
  have hinv := inv_entry_norm_le_of_box hc hd₁ hlh hcap hxw hdet
  refine ⟨fun i _ => fun j _ => ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact hent i j
  · refine ⟨((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), fun i _ => fun j _ => ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hinv i j

end GenericBox

section Adelic

variable (F : Type) [Field F] [NumberField F]

def boxedBlock (c u d₁ d₂ C : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  centreCutSiegelSet F c u d₁ d₂ ∩
    {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ C}

theorem isClosed_boxedBlock (c u d₁ d₂ C : ℝ) : IsClosed (boxedBlock F c u d₁ d₂ C) := by
  refine (isClosed_centreCutSiegelSet c u d₁ d₂).inter ?_
  have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ C}
      = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ C} := by
    ext g
    simp [Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun w =>
    isClosed_le (continuous_localHeight_place w) continuous_const

theorem isCompact_boxedBlock {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (boxedBlock F c u d₁ d₂ C) := by
  classical
  set B := Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) with hB_def
  set A : Set (AdeleRing (𝓞 F) F) :=
    (Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) B) ×ˢ
      integralFiniteAdeles (𝓞 F) F with hA_def
  set A' : Set (AdeleRing (𝓞 F) F) :=
    (Set.pi Set.univ fun w : InfinitePlace F =>
      Metric.closedBall (0 : w.Completion) (B / d₁)) ×ˢ
      integralFiniteAdeles (𝓞 F) F with hA'_def
  have hApi : IsCompact A := by
    refine IsCompact.prod (isCompact_univ_pi fun w => ?_)
      (isCompact_integralFiniteAdeles (𝓞 F) F)
    haveI := properSpace_completion (F := F) w
    exact isCompact_closedBall _ _
  have hA'pi : IsCompact A' := by
    refine IsCompact.prod (isCompact_univ_pi fun w => ?_)
      (isCompact_integralFiniteAdeles (𝓞 F) F)
    haveI := properSpace_completion (F := F) w
    exact isCompact_closedBall _ _
  set S : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A with hS_def
  set S' : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A' with hS'_def
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hApi
  have hS' : IsCompact S' := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hA'pi
  have hK : IsCompact ((Units.embedProduct
      (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ⁻¹'
      (S ×ˢ (MulOpposite.op '' S'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hS.prod (hS'.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_boxedBlock F c u d₁ d₂ C) ?_
  rintro g ⟨⟨hKf, hfloor, hwin, hdet⟩, hcap⟩
  have hKf2 := mem_finiteIntegralGL2_iff.mp hKf

  have harch : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ‖(archComponent F w (glArch (𝓞 F) F g) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ B := fun w i j =>
    entry_norm_le_of_box hc (hfloor w) (hcap w) (hwin w) (hdet w) i j
  have harch' : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ‖(((archComponent F w (glArch (𝓞 F) F g))⁻¹ : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ B / d₁ := fun w i j =>
    inv_entry_norm_le_of_box hc hd₁ (hfloor w) (hcap w) (hwin w) (hdet w) i j
  constructor
  ·
    intro i _ j _
    constructor
    · intro w _
      rw [mem_closedBall_zero_iff]
      show ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖ ≤ B
      have hbridge : ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
          = (archComponent F w (glArch (𝓞 F) F g) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
      rw [hbridge]
      exact harch w i j
    · exact hKf2.1 i j
  ·
    refine ⟨((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)),
      ?_, rfl⟩
    intro i _ j _
    constructor
    · intro w _
      rw [mem_closedBall_zero_iff]
      show ‖(((g⁻¹ : AdelicGL2 (𝓞 F) F) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖ ≤ B / d₁
      have hbridge : (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
          = (((archComponent F w (glArch (𝓞 F) F g))⁻¹ : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j := by
        have h1 : (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
            = (archComponent F w (glArch (𝓞 F) F (g⁻¹ : AdelicGL2 (𝓞 F) F)) :
                Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
        rw [h1, map_inv (glArch (𝓞 F) F), map_inv (archComponent F w)]
      rw [hbridge]
      exact harch' w i j
    · exact hKf2.2 i j

end Adelic

end M4aP1R.BoxedBlock

theorem M4aP1R.BoxedBlock.isCompact_centreCutSiegelSet_inter_heightCap_impl (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) :=
  M4aP1R.BoxedBlock.isCompact_boxedBlock F hc hd₁

theorem solution (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) := by
  exact M4aP1R.BoxedBlock.isCompact_centreCutSiegelSet_inter_heightCap_impl F hc hd₁

end
end S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
end P2MW
export P2MW.S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap (solution)
