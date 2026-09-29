-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d7e6ab8e-dd93-5126-a091-e6b84d5c1c29

import Mathlib
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem

set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem.AutomorphicForm AutomorphicForm.WindowedSiegel P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem.AutomorphicForm.WindowedSiegel"
open scoped ENNReal NNReal

namespace AutomorphicForm p2m_export "AutomorphicForm" "AdelicGL2 WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap" namespace WindowedSiegel p2m_export "AutomorphicForm.WindowedSiegel" "centreCutSiegelSet mem_centreCutSiegelSet_iff localHeight archHeight isCompact_centreCutSiegelSet_inter_heightCap" end AutomorphicForm.WindowedSiegel
p2m_open_scoped "AutomorphicForm AutomorphicForm.WindowedSiegel" in

theorem AutomorphicForm.WindowedSiegel.localHeight_archComponent_le_of_archHeight_le
    (F : Type) [Field F] [NumberField F] {c : ℝ} (hc : 0 < c)
    (g : GL (Fin 2) (InfiniteAdeleRing F))
    (hfloor : ∀ v : InfinitePlace F, c ≤ localHeight (archComponent F v g))
    {Hcap : ℝ} (hH : archHeight F g ≤ Hcap) (w : InfinitePlace F) :
    localHeight (archComponent F w g) ≤
      Hcap / (min c 1) ^ ((∑ v : InfinitePlace F, v.mult) - 1) := by
  classical
  set m : ℝ := min c 1 with hm
  have hm0 : 0 < m := lt_min hc one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmle : ∀ v : InfinitePlace F, m ≤ localHeight (archComponent F v g) :=
    fun v => (min_le_left _ _).trans (hfloor v)
  have hlh0 : ∀ v : InfinitePlace F, 0 ≤ localHeight (archComponent F v g) := fun v => hm0.le.trans (hmle v)
  set d : ℕ := ∑ v : InfinitePlace F, v.mult with hd
  have hwpos : 1 ≤ w.mult := InfinitePlace.mult_pos
  have hwle : w.mult ≤ d := Finset.single_le_sum (fun v _ => Nat.zero_le _) (Finset.mem_univ w)

  have hsplit : archHeight F g = localHeight (archComponent F w g) ^ w.mult *
      ∏ v ∈ (Finset.univ.erase w), localHeight (archComponent F v g) ^ v.mult := by
    unfold archHeight
    exact (Finset.mul_prod_erase Finset.univ (fun v => localHeight (archComponent F v g) ^ v.mult) (Finset.mem_univ w)).symm
  have hrest : m ^ (d - w.mult) ≤ ∏ v ∈ (Finset.univ.erase w), localHeight (archComponent F v g) ^ v.mult := by
    have hsum : ∑ v ∈ Finset.univ.erase w, v.mult = d - w.mult := by
      rw [hd, ← Finset.sum_erase_add _ _ (Finset.mem_univ w), Nat.add_sub_cancel]
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun v _ => pow_nonneg hm0.le _)
      (fun v _ => pow_le_pow_left₀ hm0.le (hmle v) _)
  have hw : localHeight (archComponent F w g) * m ^ (w.mult - 1) ≤ localHeight (archComponent F w g) ^ w.mult := by
    conv_rhs => rw [← Nat.sub_add_cancel hwpos, pow_succ']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0.le (hmle w) _) (hlh0 w)
  have hkey : localHeight (archComponent F w g) * m ^ (d - 1) ≤ archHeight F g := by
    have e : m ^ (d - 1) = m ^ (w.mult - 1) * m ^ (d - w.mult) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, e, ← mul_assoc]
    exact mul_le_mul hw hrest (pow_nonneg hm0.le _) (pow_nonneg (hlh0 w) _)
  rw [le_div_iff₀ (pow_pos hm0 _)]
  exact hkey.trans hH

theorem solution
    (F : Type) [Field F] [NumberField F] {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (Hcap : ℝ) :
    ∃ K₀ : Set (AdelicGL2 (𝓞 F) F), IsCompact K₀ ∧
      ∀ s ∈ centreCutSiegelSet F c u d₁ d₂, archHeight F (glArch (𝓞 F) F s) ≤ Hcap → s ∈ K₀ := by
  refine ⟨centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g))
        ≤ Hcap / (min c 1) ^ ((∑ v : InfinitePlace F, v.mult) - 1)},
    AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap F hc hd₁,
    fun s hs hH => ⟨hs, fun w => ?_⟩⟩
  exact AutomorphicForm.WindowedSiegel.localHeight_archComponent_le_of_archHeight_le F hc _
    (fun v => (mem_centreCutSiegelSet_iff.mp hs).2.1 v) hH w

end S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem (solution)
