-- Prove2me | solution 1 for AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/43826eea-7061-5a37-8b3b-9d2711281e5c

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "WindowedSiegel.archHeight AdelicGL2 globalPoints"
namespace WindowedSiegel
p2m_export "AutomorphicForm.WindowedSiegel" "rowNormSq localHeight archHeight rowNormSq_pos localHeight_pos archHeight_pos"
namespace ArthurSupport
p2m_open "AutomorphicForm.WindowedSiegel AutomorphicForm"

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem.AutomorphicForm AutomorphicForm.WindowedSiegel P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem.AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight NumberField.InfinitePlace"

section Local

variable {K : Type*} [NormedField K]

def entryNormSq (M : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2

theorem rowNormSq_mul_le (M N : Matrix (Fin 2) (Fin 2) K) :
    rowNormSq (M * N) ≤ rowNormSq M * entryNormSq N := by
  have h : ∀ j : Fin 2, ‖(M * N) 1 j‖ ^ 2
      ≤ (‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * (‖N 0 j‖ ^ 2 + ‖N 1 j‖ ^ 2) := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : ‖M 1 0 * N 0 j + M 1 1 * N 1 j‖ ≤ ‖M 1 0‖ * ‖N 0 j‖ + ‖M 1 1‖ * ‖N 1 j‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h2 : ‖M 1 0 * N 0 j + M 1 1 * N 1 j‖ ^ 2 ≤ (‖M 1 0‖ * ‖N 0 j‖ + ‖M 1 1‖ * ‖N 1 j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h2.trans ?_
    nlinarith [sq_nonneg (‖M 1 0‖ * ‖N 1 j‖ - ‖M 1 1‖ * ‖N 0 j‖), norm_nonneg (M 1 0),
      norm_nonneg (M 1 1), norm_nonneg (N 0 j), norm_nonneg (N 1 j)]
  calc rowNormSq (M * N) = ‖(M * N) 1 0‖ ^ 2 + ‖(M * N) 1 1‖ ^ 2 := rfl
    _ ≤ (‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * (‖N 0 0‖ ^ 2 + ‖N 1 0‖ ^ 2)
        + (‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * (‖N 0 1‖ ^ 2 + ‖N 1 1‖ ^ 2) := add_le_add (h 0) (h 1)
    _ = rowNormSq M * entryNormSq N := by
        unfold rowNormSq entryNormSq
        ring

def transFactor (k : GL (Fin 2) K) : ℝ :=
  entryNormSq (k : Matrix (Fin 2) (Fin 2) K) / ‖(k : Matrix (Fin 2) (Fin 2) K).det‖

private theorem aux_ineq {dg dk Rg Rgk E : ℝ} (hdk : 0 < dk) (hRg : 0 < Rg) (hRgk : 0 < Rgk)
    (hdg : 0 ≤ dg) (hle : Rgk ≤ Rg * E) : dg / Rg ≤ E / dk * (dg * dk / Rgk) := by
  rw [div_mul_div_comm, div_le_div_iff₀ hRg (mul_pos hdk hRgk)]
  have h := mul_le_mul_of_nonneg_left hle (mul_nonneg hdg hdk.le)
  calc dg * (dk * Rgk) = dg * dk * Rgk := by ring
    _ ≤ dg * dk * (Rg * E) := h
    _ = E * (dg * dk) * Rg := by ring

theorem localHeight_le_transFactor_mul (g k : GL (Fin 2) K) :
    localHeight g ≤ transFactor k * localHeight (g * k) := by
  have hRg := rowNormSq_pos g
  have hRgk := rowNormSq_pos (g * k)
  rw [Units.val_mul] at hRgk
  have hdk : 0 < ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ :=
    norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero
  unfold localHeight transFactor
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  exact aux_ineq hdk hRg hRgk (norm_nonneg _) (rowNormSq_mul_le _ _)

variable [IsTopologicalRing K]

theorem continuous_transFactor : Continuous (transFactor : GL (Fin 2) K → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) K => ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hnum : Continuous fun k : GL (Fin 2) K => entryNormSq (k : Matrix (Fin 2) (Fin 2) K) := by
    unfold entryNormSq
    exact ((((hc 0 0).pow 2).add ((hc 0 1).pow 2)).add ((hc 1 0).pow 2)).add ((hc 1 1).pow 2)
  have hdet : Continuous fun k : GL (Fin 2) K => ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ :=
    (Units.continuous_val.matrix_det).norm
  exact hnum.div hdet fun k => (norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero).ne'

end Local

section Ultrametric

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (M N : Matrix (Fin 2) (Fin 2) K) (hN : ∀ i j, ‖N i j‖ ≤ 1) :
    rowMaxNorm (M * N) ≤ rowMaxNorm M := by
  have h : ∀ j : Fin 2, ‖(M * N) 1 j‖ ≤ max ‖M 1 0‖ ‖M 1 1‖ := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hN 0 j)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hN 1 j)
  exact max_le (h 0) (h 1)

theorem finLocalHeight_mul_eq (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  have h1 : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have h2 : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, norm_one]
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : ℝ) = ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
          * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ := hprod.symm
      _ ≤ ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ := mul_one _
  have hrow : rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    refine le_antisymm ?_ ?_
    · rw [Units.val_mul]
      exact rowMaxNorm_mul_le _ _ hk
    · have hg : (g : Matrix (Fin 2) (Fin 2) K)
          = ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
              * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [← Units.val_mul, mul_inv_cancel_right]
      calc rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)
          = rowMaxNorm (((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
              * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := congrArg rowMaxNorm hg
        _ ≤ rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
            rowMaxNorm_mul_le _ _ hk'
  unfold finLocalHeight
  rw [hrow, Units.val_mul, Matrix.det_mul, norm_mul, hd, mul_one]

end Ultrametric

section Finite

variable (F : Type) [Field F] [NumberField F]

theorem finHeight_mul_of_mem (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (g * k) = finHeight F g := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_eq _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

theorem continuous_finHeight : Continuous (finHeight F) := by
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  have hopen : IsOpen ((fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => g₀⁻¹ * g) ⁻¹'
      (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) :=
    (isOpen_finiteLevelZero (𝓞 F) F (N := ⊤) top_ne_bot).preimage (continuous_const_mul g₀⁻¹)
  have hmem : g₀ ∈ ((fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => g₀⁻¹ * g) ⁻¹'
      (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) := by
    show g₀⁻¹ * g₀ ∈ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  refine (continuousAt_const : ContinuousAt (fun _ => finHeight F g₀) g₀).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with g hg
  have hg' : g₀⁻¹ * g ∈ finiteIntegralGL2 (𝓞 F) F := hg
  calc finHeight F g₀ = finHeight F (g₀ * (g₀⁻¹ * g)) := (finHeight_mul_of_mem F g₀ hg').symm
    _ = finHeight F g := by rw [mul_inv_cancel_left]

theorem exists_one_le_mul_finHeight {C : Set (AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ finiteIntegralGL2 (𝓞 F) F, ∀ k ∈ C,
      1 ≤ B * finHeight F (x * glFin (𝓞 F) F k) := by
  set Φ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) × AdelicGL2 (𝓞 F) F → ℝ :=
    fun p => (finHeight F (p.1 * glFin (𝓞 F) F p.2))⁻¹ with hΦdef
  have hΦ : Continuous Φ :=
    ((continuous_finHeight F).comp
      (continuous_fst.mul ((continuous_glFin (𝓞 F) F).comp continuous_snd))).inv₀
      fun p => (finHeight_pos _).ne'
  obtain ⟨B, hB⟩ := (((isCompact_finiteLevelZero (𝓞 F) F ⊤).prod hC).image hΦ).bddAbove
  refine ⟨max B 1, le_max_right _ _, fun x hx k hk => ?_⟩
  have h : Φ (x, k) ≤ B := hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩
  have hpos := finHeight_pos (F := F) (x * glFin (𝓞 F) F k)
  calc (1 : ℝ) = Φ (x, k) * finHeight F (x * glFin (𝓞 F) F k) := (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ max B 1 * finHeight F (x * glFin (𝓞 F) F k) :=
        mul_le_mul_of_nonneg_right (h.trans (le_max_left _ _)) hpos.le

end Finite

section Arch

variable (F : Type) [Field F] [NumberField F]

def archTransFactor (k : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ v : InfinitePlace F, transFactor (archComponent F v k) ^ v.mult

theorem archHeight_le_archTransFactor_mul (g k : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F g ≤ archTransFactor F k * archHeight F (g * k) := by
  unfold archHeight archTransFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => pow_nonneg (localHeight_pos _).le _) fun v _ => ?_
  rw [← mul_pow, map_mul]
  exact pow_le_pow_left₀ (localHeight_pos _).le (localHeight_le_transFactor_mul _ _) _

theorem continuous_archTransFactor : Continuous (archTransFactor F) := by
  unfold archTransFactor
  exact continuous_finsetProd _ fun v _ =>
    (continuous_transFactor.comp (continuous_archComponent F v)).pow _

theorem exists_archTransFactor_le {C : Set (AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k ∈ C, archTransFactor F (glArch (𝓞 F) F k) ≤ B := by
  obtain ⟨B, hB⟩ :=
    (hC.image ((continuous_archTransFactor F).comp (continuous_glArch (𝓞 F) F))).bddAbove
  exact ⟨max B 1, le_max_right _ _, fun k hk => (hB ⟨k, hk, rfl⟩).trans (le_max_left _ _)⟩

end Arch

end AutomorphicForm.WindowedSiegel.ArthurSupport

end

open scoped NumberField

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem.AutomorphicForm _root_.AutomorphicForm.WindowedSiegel _root_.P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem.AutomorphicForm.WindowedSiegel AutomorphicForm.WindowedSiegel.ArthurSupport NumberField.AdelicLevel NumberField.AdelicHeight in

theorem solution
    (F : Type) [Field F] [NumberField F]
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ T₀ : ℝ, ∀ (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F),
      NumberField.AdelicLevel.glFin (𝓞 F) F x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      NumberField.AdelicLevel.glFin (𝓞 F) F y ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F x) →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F y) →
      ∀ γ : GL (Fin 2) F,
        x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y ∈ C →
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨B₁, hB₁, hB₁C⟩ := exists_archTransFactor_le F hC
  obtain ⟨B₂, hB₂, hB₂C⟩ := exists_one_le_mul_finHeight F hC
  refine ⟨B₁ * B₂, fun x y hx hy hTx hTy γ hk => ?_⟩
  by_contra hγ

  have hγy : globalPoints (𝓞 F) F γ * y = x * (x⁻¹ * globalPoints (𝓞 F) F γ * y) := by
    rw [mul_assoc x⁻¹, mul_inv_cancel_left]

  have hle := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ y
  rw [adelicHeight_eq_archHeight_of_mem hy, hγy] at hle
  simp only [adelicHeight] at hle
  have eA : glArch (𝓞 F) F (x * (x⁻¹ * globalPoints (𝓞 F) F γ * y))
      = glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y) := map_mul _ _ _
  have eF : glFin (𝓞 F) F (x * (x⁻¹ * globalPoints (𝓞 F) F γ * y))
      = glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y) := map_mul _ _ _
  rw [eA, eF] at hle

  have h1 : archHeight F (glArch (𝓞 F) F x)
      ≤ B₁ * archHeight F (glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y)) :=
    (archHeight_le_archTransFactor_mul F _ _).trans
      (mul_le_mul_of_nonneg_right (hB₁C _ hk) (archHeight_pos F _).le)
  have h2 : 1 ≤ B₂ * finHeight F (glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y)) :=
    hB₂C _ hx _ hk
  have ha := archHeight_pos F (glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y))
  have hf := finHeight_pos (F := F)
    (glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y))
  have hB₁pos : 0 < B₁ := lt_of_lt_of_le one_pos hB₁
  have hB₁B₂ : 1 ≤ B₁ * B₂ := one_le_mul_of_one_le_of_one_le hB₁ hB₂

  have hB₂a : B₂ < archHeight F
      (glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y)) := by
    by_contra h
    push Not at h
    have h' := mul_le_mul_of_nonneg_left h hB₁pos.le
    linarith

  have haf : 1 < archHeight F
        (glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y))
      * finHeight F (glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y)) :=
    calc (1 : ℝ) ≤ B₂ * finHeight F
          (glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y)) := h2
      _ < _ := mul_lt_mul_of_pos_right hB₂a hf
  have hY : 1 < archHeight F (glArch (𝓞 F) F y) := lt_of_le_of_lt hB₁B₂ hTy
  have hlt : 1 < archHeight F
        (glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y))
      * finHeight F (glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y))
      * archHeight F (glArch (𝓞 F) F y) :=
    calc (1 : ℝ) < archHeight F
          (glArch (𝓞 F) F x * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y))
        * finHeight F (glFin (𝓞 F) F x * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y)) := haf
      _ = _ * 1 := (mul_one _).symm
      _ < _ := mul_lt_mul_of_pos_left hY (lt_trans one_pos haf)
  linarith

end S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
end P2MW
export P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem (solution)
