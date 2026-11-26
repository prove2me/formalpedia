-- Prove2me | solution 1 for Auto.shortlongJumps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:47.032567+00:00
-- url     : https://prove2.me/submissions/60653155-c26d-415d-a870-e796b6e01bde

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_lrpow_three_le
public import Theorems.Thm_Auto_aux_chainVariation_le
public import Theorems.Thm_Auto_aux_dyadicLocalChain_eq_of_mem
public import Theorems.Thm_Auto_aux_dyadicLocalChain_eq_left
public import Theorems.Thm_Auto_aux_dyadicLocal_sum_le_variation_rpow
public import Theorems.Thm_Auto_aux_dyadicPair_le_variation_rpow
public import Theorems.Thm_Auto_aux_dyadicIndex_spec
public import Theorems.Thm_Auto_aux_dyadicIndex_mono
public import Theorems.Thm_Auto_aux_mem_dyadicSet_iff
public import Theorems.Thm_Auto_aux_sum_cross_le_kappa
public import Theorems.Thm_Auto_aux_diagonal_sum_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {B : Type*} [SeminormedAddCommGroup B]
    (a : ℝ → B) (J : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    (∀ (t : Fin (J + 1) → ℝ), Monotone t → (∀ j, 0 < t j) →
      ∃ κ : Finset ℤ,
        (∀ k, k ∈ κ ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) ∧
        (∑ j : Fin J,
          (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
          2 * (∑ k ∈ κ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm
            (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J) ∧
    finiteVariationSeminorm (fun s : Set.Ioi (0 : ℝ) ↦ a s) r J ≤
      2 * (∑' k : ℤ,
        (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
      finiteVariationSeminorm
        (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
  classical
  have hlocalFinite :
      ∀ (t : Fin (J + 1) → ℝ), Monotone t → (∀ j, 0 < t j) →
        ∃ κ : Finset ℤ,
          (∀ k, k ∈ κ ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) ∧
          (∑ j : Fin J,
            (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
            2 * (∑ k ∈ κ,
              (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
            finiteVariationSeminorm
              (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
    intro t ht htpos
    let L : Fin (J + 1) → ℤ := fun j ↦ aux_dyadicIndex (t j)
    let κ : Finset ℤ := aux_dyadicSet t
    refine ⟨κ, ?_, ?_⟩
    · simpa [κ] using aux_mem_dyadicSet_iff t htpos
    have hLmono : Monotone L := by
      intro i j hij
      exact aux_dyadicIndex_mono (htpos i) (ht hij)
    let d : Fin J → ℝ≥0∞ := fun j ↦ ‖a (t j.succ) - a (t j.castSucc)‖₊
    let u : Fin J → ℝ≥0∞ := fun j ↦
      if L j.castSucc = L j.succ then
        ‖a (t j.succ) - a (t j.castSucc)‖₊
      else ‖a (t j.succ) - a ((2 : ℝ) ^ L j.succ)‖₊
    let v : Fin J → ℝ≥0∞ := fun j ↦
      ‖a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)‖₊
    let w : Fin J → ℝ≥0∞ := fun j ↦
      if L j.castSucc < L j.succ then
        ‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊
      else 0
    have hd_uvw (j : Fin J) : d j ≤ u j + v j + w j := by
      dsimp [d, u, v, w]
      by_cases hEq : L j.castSucc = L j.succ
      · simp [hEq]
      · have hle : L j.castSucc ≤ L j.succ := hLmono (Fin.castSucc_le_succ j)
        have hlt : L j.castSucc < L j.succ := lt_of_le_of_ne hle hEq
        rw [if_neg hEq, if_pos hlt]
        have hid : a (t j.succ) - a (t j.castSucc) =
            (a (t j.succ) - a ((2 : ℝ) ^ L j.succ)) +
              (a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)) +
              (a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)) := by
          abel
        rw [hid]
        have htri :
            ‖(a (t j.succ) - a ((2 : ℝ) ^ L j.succ)) +
                  (a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)) +
                  (a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc))‖₊ ≤
                ‖a (t j.succ) - a ((2 : ℝ) ^ L j.succ)‖₊ +
                  ‖a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)‖₊ +
                  ‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊ := by
          calc
            _ ≤ ‖(a (t j.succ) - a ((2 : ℝ) ^ L j.succ)) +
                  (a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc))‖₊ +
                  ‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊ :=
                nnnorm_add_le _ _
            _ ≤ _ := by
              gcongr
              exact nnnorm_add_le _ _
        exact_mod_cast htri
    have hMink := aux_lrpow_three_le r hr d u v w hd_uvw
    have hA : (∑ j : Fin J, u j ^ r) ≤
        ∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
      let F : ℤ → Fin J → ℝ≥0∞ := fun k j ↦
        (‖a (aux_dyadicLocalChain J k t j.succ) -
          a (aux_dyadicLocalChain J k t j.castSucc)‖₊ : ℝ≥0∞) ^ r
      have hlabel_mem (j : Fin J) : L j.succ ∈ κ := by
        simp [κ, aux_dyadicSet, L]
      have hdiag := aux_diagonal_sum_le (fun j ↦ L j.succ) hlabel_mem F
      have hF_le (k : ℤ) : ∑ j : Fin J, F k j ≤
          (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
        exact aux_dyadicLocal_sum_le_variation_rpow ht a r hr
      calc
        ∑ j : Fin J, u j ^ r ≤ ∑ j : Fin J, F (L j.succ) j := by
          apply Finset.sum_le_sum
          intro j _
          dsimp [u, F]
          by_cases hEq : L j.castSucc = L j.succ
          · simp only [ite_pow]
            rw [if_pos hEq]
            have hs : t j.succ ∈ Set.Icc ((2 : ℝ) ^ L j.succ)
                ((2 : ℝ) ^ (L j.succ + 1)) := by
              simpa [L] using
                ⟨(aux_dyadicIndex_spec _ (htpos j.succ)).1,
                  (aux_dyadicIndex_spec _ (htpos j.succ)).2.le⟩
            have hp : t j.castSucc ∈ Set.Icc ((2 : ℝ) ^ L j.succ)
                ((2 : ℝ) ^ (L j.succ + 1)) := by
              have hlabel : aux_dyadicIndex (t j.castSucc) =
                  aux_dyadicIndex (t j.succ) := by
                simpa [L] using hEq
              have hspec := aux_dyadicIndex_spec (t j.castSucc) (htpos j.castSucc)
              rw [hlabel] at hspec
              simpa [L] using ⟨hspec.1, hspec.2.le⟩
            rw [aux_dyadicLocalChain_eq_of_mem hs,
              aux_dyadicLocalChain_eq_of_mem hp]
          · have hle := hLmono (Fin.castSucc_le_succ j)
            have hlt : L j.castSucc < L j.succ := lt_of_le_of_ne hle hEq
            simp only [ite_pow, ge_iff_le]
            rw [if_neg hEq]
            have hs : t j.succ ∈ Set.Icc ((2 : ℝ) ^ L j.succ)
                ((2 : ℝ) ^ (L j.succ + 1)) := by
              simpa [L] using
                ⟨(aux_dyadicIndex_spec _ (htpos j.succ)).1,
                  (aux_dyadicIndex_spec _ (htpos j.succ)).2.le⟩
            have hstep : L j.castSucc + 1 ≤ L j.succ := Int.add_one_le_iff.mpr hlt
            have hpw : (2 : ℝ) ^ (L j.castSucc + 1) ≤ (2 : ℝ) ^ L j.succ :=
              (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hstep
            have hp : t j.castSucc ≤ (2 : ℝ) ^ L j.succ :=
              (aux_dyadicIndex_spec _ (htpos j.castSucc)).2.le.trans hpw
            rw [aux_dyadicLocalChain_eq_of_mem hs,
              aux_dyadicLocalChain_eq_left hp]
        _ ≤ ∑ k ∈ κ, ∑ j, F k j := hdiag
        _ ≤ ∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
          apply Finset.sum_le_sum
          intro k hk
          exact hF_le k
    have hB : (∑ j : Fin J, v j ^ r) ^ r⁻¹ ≤
        finiteVariationSeminorm
          (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
      let q : {x : Fin (J + 1) → Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) // Monotone x} :=
        ⟨fun i ↦ ⟨(2 : ℝ) ^ L i, ⟨L i, rfl⟩⟩, by
          intro i j hij
          exact (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr
            (hLmono hij)⟩
      simpa [v, q] using
        aux_chainVariation_le
          (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J q.1 q.2
    have hCsum : (∑ j : Fin J, w j ^ r) ≤
        ∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
      apply aux_sum_cross_le_kappa hLmono (fun j ↦ w j ^ r)
        (fun k ↦ (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r)
      · intro j hj
        dsimp [w]
        have hj' : ¬ L j.castSucc < L j.succ := by
          intro h
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        simp [hj', ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hr)]
      · intro j hj
        have hlt := Finset.mem_filter.mp hj |>.2
        dsimp [w]
        rw [if_pos hlt]
        let x : aux_dyadicInterval (L j.castSucc) :=
          ⟨t j.castSucc, (aux_dyadicIndex_spec _ (htpos j.castSucc)).1,
            (aux_dyadicIndex_spec _ (htpos j.castSucc)).2.le⟩
        have hp := aux_dyadicPair_le_variation_rpow (Nat.zero_lt_of_lt j.isLt) a r hr x
        have hrev :
            (‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r =
              (‖a (t j.castSucc) - a ((2 : ℝ) ^ L j.castSucc)‖₊ : ℝ≥0∞) ^ r := by
          congr 2
          apply NNReal.eq
          exact norm_sub_rev _ _
        exact hrev.trans_le (by simpa [x] using hp)
      · intro k hk
        rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
        simp [κ, aux_dyadicSet, L]
    have hC : (∑ j : Fin J, w j ^ r) ^ r⁻¹ ≤
        (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ :=
      ENNReal.rpow_le_rpow hCsum (by positivity)
    have hAsh : (∑ j : Fin J, u j ^ r) ^ r⁻¹ ≤
        (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ :=
      ENNReal.rpow_le_rpow hA (by positivity)
    calc
      (∑ j : Fin J, (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ =
          (∑ j : Fin J, d j ^ r) ^ r⁻¹ := by rfl
      _ ≤ (∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹ + (∑ j, w j ^ r) ^ r⁻¹ := hMink
      _ ≤ (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J +
          (∑ k ∈ κ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ := by
        gcongr
      _ = 2 * (∑ k ∈ κ,
        (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
        ring
  constructor
  · exact hlocalFinite
  · unfold finiteVariationSeminorm
    apply iSup_le
    intro q
    have hlocal := hlocalFinite (fun j ↦ q.1 j) q.2
      (fun j ↦ (q.1 j).2)
    rcases hlocal with ⟨κ, hκ, hlocal⟩
    calc
      (∑ j : Fin J, (‖a (q.1 j.succ) - a (q.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
          2 * (∑ k ∈ κ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
            finiteVariationSeminorm
              (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := hlocal
      _ ≤ 2 * (∑' k : ℤ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
            finiteVariationSeminorm
              (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
        gcongr
        exact ENNReal.sum_le_tsum κ
end Auto
