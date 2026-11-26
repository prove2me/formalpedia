-- Prove2me | solution 1 for ArcShortWindowEdgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:17.207822+00:00
-- url     : https://prove2.me/submissions/b9019ec2-88c0-4ed8-ab6e-2daf7d3cf7cf

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_ShortWindowAtMostOneLongEdge
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Definitions.Def_Tablet_ArcShortWindowEdgeCount
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_ShortWindowAtMostOneLongEdge
import Theorems.Thm_SplicedBreakpointShortEdgeCount


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E)
    (hcl : IsClosedCurve γ) (δ ε : ℝ) (n k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s)
    (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hlin : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ γ.len → b - a ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)).card ≤ n)
    (hwrap : ∀ a b : ℝ, 0 ≤ b → b < a → a ≤ γ.len → (γ.len - a) + b ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => (a ≤ s (j - 1) ∨ s j ≤ b) ∧ s j - s (j - 1) < δ)).card ≤ n)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len)
    (kA : ℕ) (sA : ℕ → ℝ) (hkA : 1 ≤ kA)
    (hresA : IsGeodesicResolution (curveArc γ hcl t t' ht0 htl ht'0 ht'l) kA sA)
    (hord : t ≤ t' → ∃ j0 : ℕ,
        ∀ i : ℕ, 1 ≤ i → i ≤ kA - 1 → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t)
    (hwr : t' < t → ∃ j0 m : ℕ,
        (∀ i : ℕ, 1 ≤ i → i ≤ m → j0 + (i - 1) ≤ k ∧ sA i = s (j0 + (i - 1)) - t) ∧
        (∀ i : ℕ, m < i → i ≤ kA - 1 → i - m ≤ k ∧
          sA i = (γ.len - t) + s (i - m)) ∧
        (1 ≤ m → s (j0 + (m - 1)) = γ.len))
    (hshort : sA (kA - 1) - sA 1 ≤ δ) :
    kA ≤ n + 3 := by
-- BODY
  by_cases hsmall : kA ≤ 3
  · omega
  push_neg at hsmall
  obtain ⟨hmonoA, hsA0, hsAk, -⟩ := hresA
  obtain ⟨hmonoS, hs0, hsk, -⟩ := hres
  have hmn : ∀ a b : ℕ, a ≤ b → b ≤ kA → sA a ≤ sA b := by
    intro a b hab hb
    exact hmonoA (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hb⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb⟩) hab
  have hmnS : ∀ a b : ℕ, a ≤ b → b ≤ k → s a ≤ s b := by
    intro a b hab hb
    exact hmonoS (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hb⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb⟩) hab
  -- Step 2: the window budget `W ≤ δ ≤ 2ε⁻¹δ`
  have hεinv : (1:ℝ) < ε⁻¹ := by
    have h : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε0)
    nlinarith [inv_pos.mpr hε0]
  have hbud : δ ≤ 2 * ε⁻¹ * δ := by nlinarith
  have hW : sA 1 ≤ sA (kA - 1) := hmn 1 (kA - 1) (by omega) (by omega)
  -- Step 3: at most `n` short interior edges, via correspondence with `γ`
  have hshW : ((Finset.Icc 2 (kA - 1)).filter
      (fun i => sA 1 ≤ sA (i - 1) ∧ sA i ≤ sA (kA - 1) ∧ sA i - sA (i - 1) < δ)).card ≤ n := by
    rcases le_or_gt t t' with hle | hlt
    · -- ordinary case
      obtain ⟨j0, hcorr0⟩ := hord hle
      have hj0k : j0 ≤ k := by have h := (hcorr0 1 le_rfl (by omega)).1; omega
      have ha : sA 1 - (-t) = s j0 := by
        obtain ⟨-, q⟩ := hcorr0 1 le_rfl (by omega)
        have e : j0 + (1 - 1) = j0 := by omega
        rw [e] at q; rw [q]; ring
      have hbk : j0 + (kA - 1 - 1) ≤ k := (hcorr0 (kA - 1) (by omega) le_rfl).1
      have hb : sA (kA - 1) - (-t) = s (j0 + (kA - 1 - 1)) := by
        obtain ⟨-, q⟩ := hcorr0 (kA - 1) (by omega) le_rfl
        rw [q]; ring
      refine ShiftedBreakpointShortEdgeCount k n 2 (kA - 1) j0 1 δ (-t) (sA 1) (sA (kA - 1))
        s sA (by omega) (by omega) ?_ ?_
      · intro i h1 h2
        have hidx : i + j0 - 1 = j0 + (i - 1) := by omega
        obtain ⟨p, q⟩ := hcorr0 i (by omega) h2
        rw [hidx]
        exact ⟨p, by rw [q]; ring⟩
      · refine hlin (sA 1 - (-t)) (sA (kA - 1) - (-t)) ?_ ?_ ?_ ?_
        · rw [ha, ← hs0]; exact hmnS 0 j0 (Nat.zero_le _) hj0k
        · linarith
        · rw [hb, ← hsk]; exact hmnS _ _ hbk le_rfl
        · linarith
    · -- wrap case
      obtain ⟨j0, m, htail, hhead, hsplice⟩ := hwr hlt
      have hlenA : (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len = (γ.len - t) + (t' - 0) := by
        unfold curveArc
        rw [dif_neg (not_le.mpr hlt)]
        rfl
      -- eq. (ASWEC-margin): the window is strictly shorter than the whole curve
      have hWlen : sA (kA - 1) - sA 1 < γ.len := by
        have h1 : sA (kA - 1) ≤ sA kA := hmn _ _ (by omega) le_rfl
        have h2 : sA 0 ≤ sA 1 := hmn 0 1 (by omega) (by omega)
        rw [hsAk, hlenA] at h1
        rw [hsA0] at h2
        linarith
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · -- sub-case (i): `m = 0`, the head correspondence covers every interior index
        subst hm0
        have hak : (1:ℕ) - 0 ≤ k := (hhead 1 (by omega) (by omega)).1
        have ha : sA 1 - (γ.len - t) = s (1 - 0) := by
          obtain ⟨-, q⟩ := hhead 1 (by omega) (by omega)
          rw [q]; ring
        have hbk : kA - 1 - 0 ≤ k := (hhead (kA - 1) (by omega) le_rfl).1
        have hb : sA (kA - 1) - (γ.len - t) = s (kA - 1 - 0) := by
          obtain ⟨-, q⟩ := hhead (kA - 1) (by omega) le_rfl
          rw [q]; ring
        refine ShiftedBreakpointShortEdgeCount k n 2 (kA - 1) 0 0 δ (γ.len - t) (sA 1)
          (sA (kA - 1)) s sA (by omega) (by omega) ?_ ?_
        · intro i h1 h2
          obtain ⟨p, q⟩ := hhead i (by omega) h2
          have e : i + 0 - 0 = i - 0 := by omega
          rw [e]
          exact ⟨p, by rw [q]; ring⟩
        · refine hlin (sA 1 - (γ.len - t)) (sA (kA - 1) - (γ.len - t)) ?_ ?_ ?_ ?_
          · rw [ha, ← hs0]; exact hmnS 0 _ (Nat.zero_le _) hak
          · linarith
          · rw [hb, ← hsk]; exact hmnS _ _ hbk le_rfl
          · linarith
      rcases le_or_gt (kA - 1) m with hmbig | hmsmall
      · -- sub-case (ii): `m ≥ kA - 1`, the tail correspondence covers every interior index
        have hj0k : j0 ≤ k := by have h := (htail 1 le_rfl (by omega)).1; omega
        have ha : sA 1 - (-t) = s j0 := by
          obtain ⟨-, q⟩ := htail 1 le_rfl (by omega)
          have e : j0 + (1 - 1) = j0 := by omega
          rw [e] at q; rw [q]; ring
        have hbk : j0 + (kA - 1 - 1) ≤ k := (htail (kA - 1) (by omega) hmbig).1
        have hb : sA (kA - 1) - (-t) = s (j0 + (kA - 1 - 1)) := by
          obtain ⟨-, q⟩ := htail (kA - 1) (by omega) hmbig
          rw [q]; ring
        refine ShiftedBreakpointShortEdgeCount k n 2 (kA - 1) j0 1 δ (-t) (sA 1) (sA (kA - 1))
          s sA (by omega) (by omega) ?_ ?_
        · intro i h1 h2
          have hidx : i + j0 - 1 = j0 + (i - 1) := by omega
          obtain ⟨p, q⟩ := htail i (by omega) (by omega)
          rw [hidx]
          exact ⟨p, by rw [q]; ring⟩
        · refine hlin (sA 1 - (-t)) (sA (kA - 1) - (-t)) ?_ ?_ ?_ ?_
          · rw [ha, ← hs0]; exact hmnS 0 j0 (Nat.zero_le _) hj0k
          · linarith
          · rw [hb, ← hsk]; exact hmnS _ _ hbk le_rfl
          · linarith
      · -- sub-case (iii): `1 ≤ m ≤ kA - 2`, both correspondences are live and meet at the splice
        have hj0k : j0 ≤ k := by have h := (htail 1 le_rfl (by omega)).1; omega
        have ha : sA 1 - (-t) = s j0 := by
          obtain ⟨-, q⟩ := htail 1 le_rfl (by omega)
          have e : j0 + (1 - 1) = j0 := by omega
          rw [e] at q; rw [q]; ring
        have hbk : kA - 1 - m ≤ k := (hhead (kA - 1) (by omega) le_rfl).1
        have hb : sA (kA - 1) - (γ.len - t) = s (kA - 1 - m) := by
          obtain ⟨-, q⟩ := hhead (kA - 1) (by omega) le_rfl
          rw [q]; ring
        refine SplicedBreakpointShortEdgeCount k n kA j0 m δ (-t) (γ.len - t) (sA 1)
          (sA (kA - 1)) s sA hmonoS hs0 (by omega) (by omega) ?_ ?_ ?_ ?_ ?_
        · intro i h1 h2
          obtain ⟨p, q⟩ := htail i h1 h2
          exact ⟨p, by rw [q]; ring⟩
        · intro i h1 h2
          obtain ⟨p, q⟩ := hhead i h1 h2
          exact ⟨p, by rw [q]; ring⟩
        · rw [hsplice (by omega)]; ring
        · linarith
        · refine hwrap (sA 1 - (-t)) (sA (kA - 1) - (γ.len - t)) ?_ ?_ ?_ ?_
          · rw [hb, ← hs0]; exact hmnS 0 _ (Nat.zero_le _) hbk
          · linarith
          · rw [ha, ← hsk]; exact hmnS j0 k hj0k le_rfl
          · linarith
  -- Step 3': the window conjuncts are automatic on `{2,…,kA-1}` by monotonicity of `sA`
  have hsh : ((Finset.Icc 2 (kA - 1)).filter (fun i => sA i - sA (i - 1) < δ)).card ≤ n := by
    refine le_trans (Finset.card_le_card ?_) hshW
    intro i hi
    obtain ⟨hiI, hs⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi2, hiK⟩ := Finset.mem_Icc.mp hiI
    exact Finset.mem_filter.mpr ⟨hiI, hmn 1 (i - 1) (by omega) (by omega),
      hmn i (kA - 1) hiK (by omega), hs⟩
  -- Step 1: at most one long interior edge
  have hlg := ShortWindowAtMostOneLongEdge kA sA δ hδ hmonoA hshort
  -- Step 4: assembly
  have hsub : (Finset.Icc 2 (kA - 1)) ⊆
      ((Finset.Icc 2 (kA - 1)).filter (fun i => sA i - sA (i - 1) < δ)) ∪
      ((Finset.Icc 2 (kA - 1)).filter (fun i => δ ≤ sA i - sA (i - 1))) := by
    intro i hi
    rcases lt_or_ge (sA i - sA (i - 1)) δ with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, h⟩)
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Nat.card_Icc] at hcard
  omega
