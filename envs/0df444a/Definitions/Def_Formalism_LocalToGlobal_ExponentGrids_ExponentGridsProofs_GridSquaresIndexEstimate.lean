-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_GridSquaresIndexEstimate
-- name    : Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_GridSquaresIndexEstimate
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:24.228416+00:00
-- url     : https://prove2.me/theorems/ae672bf8-6c11-491b-8aba-b60deb19f131
-- title:
--   Grid Squares Index Estimate
-- statement:
--   Definitions and structural lemmas for Grid Squares Index Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ExponentGridsProofs/GridSquaresIndexEstimate.lean

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExplicitSizeInequalityIndexed
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_ValuationRatioIndex
import Theorems.Thm_Formalism_AtG_grid_ell_bound
import Theorems.Thm_Formalism_AtG_j3Wt
import Theorems.Thm_Formalism_AtG_partial_ht
import Theorems.Thm_Formalism_AtG_partial_nat
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_lw_nonneg
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_natCast_nonneg
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_prod
import Theorems.Thm_Formalism_ValuationGridEstimates_grid_index_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
namespace Formalism.AtG
theorem grid_squares_index_estimate (W S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (vr vA vA' : W → Fin m × Fin m → ℝ) (vT : W → Fin m × Fin m → ℤ → ℝ)
    (vTd : W → Fin m × Fin m → Bool → ℤ → ℝ)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (B BN Bδ : ℝ) (W0 : Finset W)
    (hlam : ∀ w, 0 ≤ lam w) (hδ : ∀ w, 0 ≤ δ w) (hN0 : ∀ ij s l, 0 ≤ N0 ij s l)
    (hvq : ∀ w s, 0 ≤ vq w s) (hprime : ∀ w, (ell w).Prime)
    (hfib : ∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l)
    (hdh : ∀ ij, dd ij = 2 * hh ij) (hdd : ∀ ij, dd ij ≤ 2 * N) (hyy : ∀ ij, yy ij ≤ m)
    (hcc : ∀ s ∈ S0, cc s ≤ ee s)
    (hsq : ∀ w ∈ W0, ∀ ij, vr w ij ≤ |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij (ch w) s|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ + 6 * δ w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * vq w s))
    (hA : ∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA w ij| ≤ B)
    (hA' : ∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA' w ij| ≤ B)
    (hT : ∀ ij s (F : Finset W), ∑ w ∈ F, lam w * |vT w ij s| ≤ B)
    (hTd : ∀ ij b s (F : Finset W), ∑ w ∈ F, lam w * |vTd w ij b s| ≤ B)
    (hBN : ∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 ij s l * Real.log l ≤ BN)
    (hBδ : ∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ)
    (hq : ∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) :
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 10 * N * BN + 2 * N + 6 * Bδ +
        4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) := by
  classical
  by_cases hm : m = 0
  · subst hm
    simp
  let vx : W → ((Fin m × Fin m) × Bool) × (Bool ⊕ (Fin 4 × ℤ × Bool)) → ℝ := fun w x =>
    match x.2 with
    | Sum.inl false => vA w x.1.1
    | Sum.inl true => vA' w x.1.1
    | Sum.inr (_, s, false) => vT w x.1.1 s
    | Sum.inr (_, s, true) => vTd w x.1.1 x.1.2 s
  let XX : Fin m × Fin m → Bool → Finset (((Fin m × Fin m) × Bool) × (Bool ⊕ (Fin 4 × ℤ × Bool))) := fun ij b =>
    ({(ij, b)} : Finset ((Fin m × Fin m) × Bool)) ×ˢ
      ((Finset.univ : Finset Bool).disjSum
        ((Finset.univ : Finset (Fin 4)) ×ˢ (Icc (1 : ℤ) (hh ij) ×ˢ (Finset.univ : Finset Bool))))
  have hB0 : 0 ≤ B := by
    have ij : Fin m × Fin m := (⟨0, by omega⟩, ⟨0, by omega⟩)
    simpa using hA ij ∅
  have hsumXX : ∀ w ij b, ∑ x ∈ XX ij b, |vx w x| = |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij b s|)) := by
    intro w ij b
    simp only [XX, sum_product, sum_singleton, sum_disjSum, Fintype.sum_bool, vx, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have : ∑ s ∈ Icc (1 : ℤ) (hh ij), (|vTd w ij b s| + |vT w ij s|) =
        ∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij b s|) :=
      sum_congr rfl (fun s _ => add_comm _ _)
    rw [this]; ring
  have hcardXX : ∀ ij b, (XX ij b).card ≤ 2 + 8 * N := by
    intro ij b
    simp only [XX, card_product, card_singleton, card_disjSum, card_univ, Fintype.card_bool,
      Fintype.card_fin, Int.card_Icc]
    have h1 := hdh ij
    have h2 := hdd ij
    have : ((hh ij : ℤ) + 1 - 1).toNat = hh ij := by omega
    rw [this]; omega
  have key := Formalism.ValuationGridEstimates.grid_index_bound W _ S m N lam δ ell N0 vr vx XX ch dd hh yy S0 cc ee qq vq
    (fun _ => B) BN Bδ W0 hlam hδ hN0 hvq hprime hfib hdh hdd hyy hcc
    (by
      intro w hw ij
      rw [hsumXX]
      have := hsq w hw ij
      linarith)
    (by
      rintro ⟨⟨ij, b⟩, (t | ⟨k, s, t⟩)⟩ F
      · cases t
        · exact hA ij F
        · exact hA' ij F
      · cases t
        · exact hT ij s F
        · exact hTd ij b s F)
    hBN hBδ hq
  have hX : ∑ ij : Fin m × Fin m, ∑ b : Bool, ∑ _x ∈ XX ij b, B ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B) := by
    calc ∑ ij : Fin m × Fin m, ∑ b : Bool, ∑ _x ∈ XX ij b, B
        ≤ ∑ _ij : Fin m × Fin m, ∑ _b : Bool, (2 + 8 * (N : ℝ)) * B := by
          apply sum_le_sum; intro ij _
          apply sum_le_sum; intro b _
          rw [sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hB0
          exact_mod_cast hcardXX ij b
      _ = _ := by
          simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
            nsmul_eq_mul]
          push_cast; ring
  linarith
theorem gridHeightBoundIndexed : GridHeightBoundIndexed := by
  intro K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh yy S0 cc ee qq B BN0 Bδ W0
    hdl hS hN0 hSe hrr hdd hddN hyy hcc hsq hA hT hTd hBN00 hBN0 hBδ
  obtain ⟨ell, hell⟩ := grid_ell_bound K
  classical
  have he : ∀ w : Pl K, (0 : ℝ) < (vw w (ell w : K) : ℝ) := by
    intro w
    have := (hell w).2
    unfold Formalism.DivisionValues.PlOver at this
    exact_mod_cast this
  have hlam : ∀ (w : Pl K) (t : ℝ),
      lw w * (vw w (ell w : K) : ℝ) * (t / (vw w (ell w : K) : ℝ)) = lw w * t := by
    intro w t
    have := (he w).ne'
    field_simp
  have habs : ∀ (w : Pl K) (t : ℝ),
      |t / (vw w (ell w : K) : ℝ)| = |t| / (vw w (ell w : K) : ℝ) := by
    intro w t
    rw [abs_div, abs_of_pos (he w)]
  obtain ⟨N1, hN1⟩ : ∃ f : Fin m × Fin m → ℤ → ℕ → ℝ, ∀ ij s l,
      f ij s l = if 1 ≤ s ∧ s ≤ (hh ij : ℤ) ∧ l ∈ S then N0 ij s l else 0 :=
    ⟨_, fun _ _ _ => rfl⟩
  have hN1in : ∀ ij (s : ℤ) l, 1 ≤ s → s ≤ (hh ij : ℤ) → l ∈ S → N1 ij s l = N0 ij s l := by
    intro ij s l a1 a2 a3
    rw [hN1, if_pos ⟨a1, a2, a3⟩]
  have hN1S : ∀ ij (s : ℤ) l, l ∉ S → N1 ij s l = 0 := by
    intro ij s l a3
    rw [hN1, if_neg (fun h => a3 h.2.2)]
  have hN1s : ∀ ij (s : ℤ) l, ¬ (1 ≤ s ∧ s ≤ (hh ij : ℤ)) → N1 ij s l = 0 := by
    intro ij s l a3
    rw [hN1, if_neg (fun h => a3 ⟨h.1, h.2.1⟩)]
  have hN1nn : ∀ ij s l, 0 ≤ N1 ij s l := by
    intro ij s l
    rw [hN1]
    split_ifs with h
    · exact hN0 ij s h.1 h.2.1 l h.2.2
    · exact le_rfl
  have hbud : ∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, N1 ij s l * Real.log l ≤ BN0 := by
    intro ij s P _
    by_cases hs : 1 ≤ s ∧ s ≤ (hh ij : ℤ)
    · refine le_trans ?_ (hBN0 ij s hs.1 hs.2)
      have h1 : ∑ l ∈ P, N1 ij s l * Real.log l =
          ∑ l ∈ P.filter (· ∈ S), N0 ij s l * Real.log l := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : l ∈ S
        · rw [if_pos hl, hN1in ij s l hs.1 hs.2 hl]
        · rw [if_neg hl, hN1S ij s l hl, zero_mul]
      rw [h1]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        exact (Finset.mem_filter.1 hl).2
      · intro l hl _
        exact mul_nonneg (hN0 ij s hs.1 hs.2 l hl) (Real.log_natCast_nonneg l)
    · refine le_trans (le_of_eq ?_) hBN00
      apply Finset.sum_eq_zero
      intro l _
      rw [hN1s ij s l hs, zero_mul]
  have key := grid_squares_index_estimate (Pl K) Sq m N
    (fun w => lw w * (vw w (ell w : K) : ℝ)) (fun w => dl w / (vw w (ell w : K) : ℝ)) ell
    N1
    (fun w ij => (vw w (rr w ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA' ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij s => ((vw w (zT ij s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij b s => ((vw w (zTd ij b s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    ch dd hh yy S0 cc ee qq
    (fun w s => (vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) B BN0 Bδ W0
    (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (he w).le)
    (fun w => div_nonneg (hdl w) (he w).le)
    hN1nn
    (fun w s => div_nonneg (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w (qq s)) (he w).le)
    (fun w => (hell w).1)
    (fun l F hF => by
      refine le_trans (le_of_eq ?_) (partial_nat K l F)
      apply Finset.sum_congr rfl
      intro w hw
      rw [hF w hw])
    hdd hddN hyy hcc
    (fun w hw ij => by
      have hE := he w
      have h0 := hsq w hw ij
      have hs3 : ∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w =
          (∑ s ∈ Icc (1 : ℤ) (hh ij), N1 ij s (ell w)) * (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_Icc] at hs
        rw [j3Wt K ell hell S (N0 ij s) hS w]
        by_cases hl : ell w ∈ S
        · rw [if_pos hl, hN1in ij s _ hs.1 hs.2 hl]
        · rw [if_neg hl, hN1S ij s _ hl]
      rw [hs3, j3Wt K ell hell Se (fun l => 1 / (l : ℝ) ^ 2) hSe w] at h0
      simp only [habs]
      have hs1 : ∑ s ∈ Icc (1 : ℤ) (hh ij),
          (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ) +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      have hs2 : ∑ s ∈ S0, (cc s : ℝ) * ((vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hs1, hs2, div_le_iff₀ hE]
      refine le_trans h0 ?_
      generalize (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) = T1
      generalize (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) = T2
      generalize (∑ s ∈ Icc (1 : ℤ) (hh ij), N1 ij s (ell w)) = T3
      generalize (vw w (ell w : K) : ℝ) = E at hE ⊢
      have hε : (if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) ≤ (((ell w : ℕ) : ℝ) ^ 2)⁻¹ := by
        split_ifs
        · rw [one_div]
        · positivity
      have hdd0 : (0 : ℝ) ≤ (dd ij : ℝ) := Nat.cast_nonneg _
      have h5 : (dd ij : ℝ) * ((if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) * E) ≤
          (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε hE.le) hdd0
      have h6 : (|(vw w (zA ij) : ℝ)| / E + |(vw w (zA' ij) : ℝ)| / E + 4 * (T1 / E) +
          5 * T3 + (dd ij : ℝ) * (((ell w : ℕ) : ℝ) ^ 2)⁻¹ +
          6 * (dl w / E) + (yy ij : ℝ) * (2 * (T2 / E))) * E =
          |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| + 4 * T1 +
          5 * (T3 * E) + (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) +
          6 * dl w + (yy ij : ℝ) * (2 * T2) := by
        have := hE.ne'
        field_simp
      rw [h6]
      linarith)
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).1 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).2 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hT ij s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    (fun ij b s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hTd ij b s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    hbud
    (fun F => by
      refine le_trans (le_of_eq ?_) (hBδ F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
    (fun s _ F => by
      refine le_trans (le_of_eq ?_) (partial_nat K (qq s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
  unfold gridBudgetIdx
  refine le_trans (le_of_eq ?_) key
  apply Finset.sum_congr rfl
  intro w _
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w Finset.univ (fun ij => rr w ij) (fun ij _ => hrr w ij), ← Finset.sum_div, hlam]
  push_cast
  rfl
example (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (W0 : Finset (Pl K)) :
    ∑ w ∈ W0, lw w * (vw w (∏ _ij : Fin 1 × Fin 1, (32 : K)) : ℝ) ≤
      gridBudgetIdx 1 1 0 (Real.log 2) 0 (∅ : Finset Empty) (fun _ => 0) (fun _ => 0) := by
  have hone : ∀ w : Pl K, vw w (1 : K) = 0 := fun w => (Formalism.DivisionValues.valuation_basic_properties K w).2.2.2.2.1
  have hHt : HtLe (K := K) (fun _ => 0) 1 0 := by
    unfold Formalism.PairingDivisionLocalBalance.HtLe
    simp [hone]
  refine gridHeightBoundIndexed K Empty 1 1 (fun _ => 0) {2} ∅ (fun _ _ _ => 1) (fun _ _ => 32) (fun _ => 1)
    (fun _ => 1) (fun _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 0) (fun _ => false) (fun _ => 2)
    (fun _ => 1) (fun _ => 0) ∅ (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 (Real.log 2) 0 W0
    (fun _ => le_rfl) (by simp [Nat.prime_two]) (fun _ _ _ _ _ _ => zero_le_one) (by simp)
    (fun _ _ => by norm_num) (fun _ => rfl) (fun _ => le_rfl) (fun _ => Nat.zero_le _) (by simp)
    ?_ (fun _ => ⟨hHt, hHt⟩) (fun _ _ => hHt) (fun _ _ _ => hHt) (Real.log_nonneg (by norm_num))
    (fun _ _ _ _ => by simp) (fun _ => by simp)
  intro w _ ij
  have vmul := (Formalism.DivisionValues.valuation_basic_properties K w).1
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h32 : vw w (32 : K) = 5 * vw w (2 : K) := by
    have e : (32 : K) = 2 * (2 * (2 * (2 * 2))) := by norm_num
    rw [e, vmul _ _ h2 (by norm_num), vmul _ _ h2 (by norm_num), vmul _ _ h2 (by norm_num),
      vmul _ _ h2 h2]
    ring
  simp [hone, h32, Formalism.PairingDivisionLocalBalance.wt]
end Formalism.AtG


