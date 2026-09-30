-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFeasibleImbalance
-- name    : CK_GeneralCK_PsiFeasibleImbalance
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:46:45.587627+00:00
-- url     : https://prove2.me/theorems/0e162603-4ada-403c-b6cf-08a70026981a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFeasibleImbalance` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFeasibleImbalance` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFeasibleImbalance` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFeasibleImbalance (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFeasibleImbalance.lean)

import Definitions.Def_CK_GeneralCK_PsiLogSumOwner

-- ===== source module GeneralCK.PsiFeasibleImbalance =====
section

/-!
# The feasible child-entropy imbalance

This proves manuscript equation (108).  If one child entropy cap is below
the average deficit, equal deficits are infeasible.  Retaining the closest
feasible split gives a stronger bound than unrestricted Jensen.
-/

namespace GeneralCK
open Set

namespace Scalar

theorem feasible_imbalance_args_mem {x y A D : ℝ}
    (hx : x ∈ Ico (0:ℝ) 1) (hy : y ∈ Ico (0:ℝ) 1)
    (hxA : x ≤ A) (hyD : y ≤ D) :
    let s := (x+y)/2
    let r := max 0 (s-min A D)
    (s-r) ∈ Ico (0:ℝ) 1 ∧ (s+r) ∈ Ico (0:ℝ) 1 := by
  dsimp only
  have hs : 0 ≤ (x+y)/2 := by linarith [hx.1, hy.1]
  have hs1 : (x+y)/2 < 1 := by linarith [hx.2, hy.2]
  have hc : 0 ≤ min A D := le_min (hx.1.trans hxA) (hy.1.trans hyD)
  by_cases hr : (x+y)/2 ≤ min A D
  · rw [max_eq_left (by linarith : (x+y)/2-min A D ≤ 0)]
    simp only [sub_zero, add_zero]
    exact ⟨⟨hs, hs1⟩, ⟨hs, hs1⟩⟩
  · rw [max_eq_right (by linarith : 0 ≤ (x+y)/2-min A D)]
    have hu : x+y-min A D < 1 := by
      rcases le_total A D with hAD | hDA
      · rw [min_eq_left hAD]
        linarith [hy.2]
      · rw [min_eq_right hDA]
        linarith [hx.2]
    constructor <;> constructor <;> linarith

theorem profile_pair_contract {x y z : ℝ} (hx : x ∈ Ico (0:ℝ) 1)
    (hy : y ∈ Ico (0:ℝ) 1) (hxz : x ≤ z) (hzy : z ≤ y) :
    P z+P (x+y-z) ≤ P x+P y := by
  by_cases hxy : x=y
  · have hz : z=x := by linarith
    simp [hz, hxy]
  have hd : 0 < y-x := sub_pos.mpr (lt_of_le_of_ne (hxz.trans hzy) hxy)
  let t := (z-x)/(y-x)
  have ht : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have h₁ := P_convexOn.2 hx hy (sub_nonneg.mpr ht1) ht
    (show (1-t)+t=1 by ring)
  have h₂ := P_convexOn.2 hx hy ht (sub_nonneg.mpr ht1)
    (show t+(1-t)=1 by ring)
  have he₁ : (1-t)*x+t*y=z := by dsimp [t]; field_simp; ring
  have he₂ : t*x+(1-t)*y=x+y-z := by dsimp [t]; field_simp; ring
  simp only [smul_eq_mul] at h₁ h₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  linarith

/-- The exact constrained Jensen inequality, stated directly in deficits.
The two profile arguments produced by `r` are guaranteed to remain physical
by the child caps. -/
theorem feasible_imbalance_lower {x y A D : ℝ}
    (hx : x ∈ Ico (0:ℝ) 1) (hy : y ∈ Ico (0:ℝ) 1)
    (hxA : x ≤ A) (hyD : y ≤ D) :
    let s := (x+y)/2
    let r := max 0 (s-min A D)
    (P (s-r)+P (s+r))/2 ≤ (P x+P y)/2 := by
  dsimp only
  by_cases hc : (x+y)/2 ≤ min A D
  · rw [max_eq_left (by linarith : (x+y)/2-min A D ≤ 0)]
    have h := P_convexOn.2 hx hy
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    simp only [smul_eq_mul, sub_zero, add_zero] at h ⊢
    have he : (1/2:ℝ)*x+(1/2)*y=(x+y)/2 := by ring
    rw [he] at h
    linarith
  · have hc' : min A D < (x+y)/2 := lt_of_not_ge hc
    rw [max_eq_right (by linarith : 0 ≤ (x+y)/2-min A D)]
    have h₁ : (x+y)/2-((x+y)/2-min A D)=min A D := by ring
    have h₂ : (x+y)/2+((x+y)/2-min A D)=x+y-min A D := by ring
    rw [h₁, h₂]
    rcases le_total A D with hAD | hDA
    · rw [min_eq_left hAD] at hc' ⊢
      have h := profile_pair_contract hx hy hxA (by linarith)
      linarith
    · rw [min_eq_right hDA] at hc' ⊢
      have h := profile_pair_contract hy hx hyD (by linarith)
      rw [add_comm y x] at h
      linarith

end Scalar

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

noncomputable def forcedDeficitImbalance (μ : InteriorLaw ι) : ℝ :=
  max 0 (μ.meanDeficit-min (H μ.a) (H μ.b))

noncomputable def capSensitiveSplitBound (μ : InteriorLaw ι) : ℝ :=
  Scalar.P μ.information -
    (Scalar.P (μ.meanDeficit-μ.forcedDeficitImbalance)+
      Scalar.P (μ.meanDeficit+μ.forcedDeficitImbalance))/2

theorem capSensitive_profile_args_mem (μ : InteriorLaw ι) :
    (μ.meanDeficit-μ.forcedDeficitImbalance) ∈ Ico (0:ℝ) 1 ∧
      (μ.meanDeficit+μ.forcedDeficitImbalance) ∈ Ico (0:ℝ) 1 :=
  Scalar.feasible_imbalance_args_mem μ.left_deficit_mem μ.right_deficit_mem
    (by linarith [μ.e_pos]) (by linarith [μ.f_pos])

theorem capSensitiveSplitBound_le_splitBound (μ : InteriorLaw ι) :
    μ.capSensitiveSplitBound ≤ μ.splitBound := by
  have hm := μ.capSensitive_profile_args_mem
  have h := Scalar.P_convexOn.2 hm.1 hm.2
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1/2:ℝ)*(μ.meanDeficit-μ.forcedDeficitImbalance)+
      (1/2)*(μ.meanDeficit+μ.forcedDeficitImbalance)=μ.meanDeficit := by ring
  rw [he] at h
  unfold capSensitiveSplitBound splitBound
  rw [μ.information_eq]
  linarith

theorem feasible_child_profile_lower (μ : InteriorLaw ι) :
    (Scalar.P (μ.meanDeficit-μ.forcedDeficitImbalance)+
      Scalar.P (μ.meanDeficit+μ.forcedDeficitImbalance))/2 ≤
    (Scalar.P (H μ.a-μ.e)+Scalar.P (H μ.b-μ.f))/2 := by
  exact Scalar.feasible_imbalance_lower μ.left_deficit_mem μ.right_deficit_mem
    (by linarith [μ.e_pos]) (by linarith [μ.f_pos])

theorem psi_gap_le_capSensitiveSplitBound (μ : InteriorLaw ι) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.capSensitiveSplitBound := by
  have h := μ.feasible_child_profile_lower
  simp only [candidateGap, psi_eq_P]
  change Scalar.P μ.information-_ ≤ _
  unfold capSensitiveSplitBound
  linarith

/-- The new comparison retains the cap-forced imbalance in the active
parent branch.  Its remaining scalar premise is suitable for finite boxes. -/
theorem gap_le_of_activePsi_of_capSensitiveSplitBound_le_interiorCost
    (μ : InteriorLaw ι)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy)
    (hscalar : μ.capSensitiveSplitBound ≤ interiorCost μ.a μ.b) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hactive).trans
    (μ.psi_gap_le_capSensitiveSplitBound.trans
      (hscalar.trans (μ.interiorCost_le_psiLogSumCostFloor.trans
        μ.psiLogSumCostFloor_le_cost)))

end InteriorLaw

#print axioms Scalar.feasible_imbalance_lower
#print axioms InteriorLaw.capSensitiveSplitBound_le_splitBound
#print axioms InteriorLaw.psi_gap_le_capSensitiveSplitBound
#print axioms InteriorLaw.gap_le_of_activePsi_of_capSensitiveSplitBound_le_interiorCost

end GeneralCK

end


