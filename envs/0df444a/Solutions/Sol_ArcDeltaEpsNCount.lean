-- Prove2me | solution 1 for ArcDeltaEpsNCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:38.117785+00:00
-- url     : https://prove2.me/submissions/00d961ba-1aaf-4a6f-8f4d-79727cc10ae4

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ClampedLinearShortEdgeCount
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Definitions.Def_Tablet_ArcDeltaEpsNCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ClampedLinearShortEdgeCount
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_SplicedBreakpointShortEdgeCount


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E)
    (hcl : IsClosedCurve γ) (δ ε : ℝ) (n k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s)
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
    (h1 : 0 ≤ sA 1) (h1k : sA 1 ≤ sA (kA - 1))
    (hkl : sA (kA - 1) ≤ (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len)
    (hnc : ¬ IsClosedCurve
      (curveRestrict (curveArc γ hcl t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) h1 h1k hkl)) :
    IsDeltaEpsN
      (curveRestrict (curveArc γ hcl t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) h1 h1k hkl)
      δ ε n := by
-- BODY
  obtain ⟨hmonoA, hsA0, hsAk, -⟩ := id hresA
  obtain ⟨hmonoS, hs0, hsk, -⟩ := id hres
  have hmn : ∀ x y : ℕ, x ≤ y → y ≤ kA → sA x ≤ sA y := by
    intro x y hxy hy
    exact hmonoA (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hxy hy⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hy⟩) hxy
  have hmnS : ∀ x y : ℕ, x ≤ y → y ≤ k → s x ≤ s y := by
    intro x y hxy hy
    exact hmonoS (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hxy hy⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hy⟩) hxy
  have hslow : ∀ j : ℕ, j ≤ k → 0 ≤ s j := by
    intro j hj; rw [← hs0]; exact hmnS 0 j (Nat.zero_le _) hj
  have hshigh : ∀ j : ℕ, j ≤ k → s j ≤ γ.len := by
    intro j hj; rw [← hsk]; exact hmnS j k hj le_rfl
  -- the clamped-linear bound: `hlin` at an arbitrary, unclamped window of the same length
  have hclamp : ∀ x y : ℝ, y - x ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => x ≤ s (j - 1) ∧ s j ≤ y ∧ s j - s (j - 1) < δ)).card ≤ n :=
    fun x y hxy => ClampedLinearShortEdgeCount k n δ ε γ.len s hmonoS hslow hshigh hlin x y hxy
  -- `kA = 1` is impossible: it would make the sub-window a single point, hence closed
  have hkA2 : 2 ≤ kA := by
    rcases Nat.lt_or_ge kA 2 with hlt2 | hge2
    · exfalso
      have hk1 : kA = 1 := by omega
      have he : sA (kA - 1) = 0 := by rw [hk1]; exact hsA0
      have h1e : sA 1 = 0 := le_antisymm (by rw [he] at h1k; exact h1k) h1
      apply hnc
      have hlen0 : (curveRestrict (curveArc γ hcl t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1))
          h1 h1k hkl).len = 0 := by
        show sA (kA - 1) - sA 1 = 0
        rw [he, h1e]; ring
      unfold IsClosedCurve
      rw [hlen0]
    · exact hge2
  -- the whole linear counting clause, stated in the reindexed (`sA`-side) form
  have key : ∀ c1 c2 : ℝ, 0 ≤ c1 → c1 ≤ c2 → c2 ≤ sA (kA - 1) - sA 1 → c2 - c1 ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 (kA - 1 - 1)).filter
        (fun j => c1 ≤ sA (1 + (j - 1)) - sA 1 ∧ sA (1 + j) - sA 1 ≤ c2 ∧
          (sA (1 + j) - sA 1) - (sA (1 + (j - 1)) - sA 1) < δ)).card ≤ n := by
    intro c1 c2 hc1 hc12 hc2len hgap
    have hmain : ((Finset.Icc 2 (kA - 1)).filter
        (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
          sA i - sA (i - 1) < δ)).card ≤ n := by
      rcases le_or_gt t t' with hle | hlt
      · -- ordinary case: one affine reindexing covers every interior index
        obtain ⟨j0, hcorr0⟩ := hord hle
        refine ShiftedBreakpointShortEdgeCount k n 2 (kA - 1) j0 1 δ (-t)
          (c1 + sA 1) (c2 + sA 1) s sA (by omega) (by omega) ?_ ?_
        · intro i hi1 hi2
          have hidx : i + j0 - 1 = j0 + (i - 1) := by omega
          obtain ⟨pp, qq⟩ := hcorr0 i (by omega) hi2
          rw [hidx]
          exact ⟨pp, by rw [qq]; ring⟩
        · exact hclamp _ _ (by linarith)
      · -- wrap case: the arc crosses `γ`'s basepoint, so the correspondence splits at `m`
        obtain ⟨j0, m, htail, hhead, hsplice⟩ := hwr hlt
        have hlenA : (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len = (γ.len - t) + (t' - 0) := by
          unfold curveArc
          rw [dif_neg (not_le.mpr hlt)]
          rfl
        have hAlt : (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len < γ.len := by
          rw [hlenA]; linarith
        have hgapsmall : c2 - c1 < γ.len := by linarith
        -- the head stretch alone, at the widened shifted helper with `(c,d) = (0,m)`
        have hHbound : ((Finset.Icc (max 2 (m + 1)) (kA - 1)).filter
            (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
              sA i - sA (i - 1) < δ)).card ≤ n := by
          refine ShiftedBreakpointShortEdgeCount k n (max 2 (m + 1)) (kA - 1) 0 m δ (γ.len - t)
            (c1 + sA 1) (c2 + sA 1) s sA (by omega) (by omega) ?_ ?_
          · intro i hi1 hi2
            rcases Nat.lt_or_ge m i with hmi | hmi
            · obtain ⟨pp, qq⟩ := hhead i hmi hi2
              have e : i + 0 - m = i - m := by omega
              rw [e]
              exact ⟨pp, by rw [qq]; ring⟩
            · have him : i = m := by omega
              have hm1 : 1 ≤ m := by omega
              obtain ⟨pp, qq⟩ := htail m hm1 le_rfl
              have e : i + 0 - m = 0 := by omega
              refine ⟨by omega, ?_⟩
              rw [e, hs0, him, qq, hsplice hm1]
              ring
          · exact hclamp _ _ (by linarith)
        -- the tail stretch alone, at the widened shifted helper with `(c,d) = (j0,1)`
        have hTbound : ((Finset.Icc 2 m).filter
            (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
              sA i - sA (i - 1) < δ)).card ≤ n := by
          refine ShiftedBreakpointShortEdgeCount k n 2 m j0 1 δ (-t)
            (c1 + sA 1) (c2 + sA 1) s sA (by omega) (by omega) ?_ ?_
          · intro i hi1 hi2
            have hidx : i + j0 - 1 = j0 + (i - 1) := by omega
            obtain ⟨pp, qq⟩ := htail i (by omega) hi2
            rw [hidx]
            exact ⟨pp, by rw [qq]; ring⟩
          · exact hclamp _ _ (by linarith)
        have hsubF : ((Finset.Icc 2 (kA - 1)).filter
              (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
                sA i - sA (i - 1) < δ)) ⊆
            ((Finset.Icc 2 m).filter
              (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
                sA i - sA (i - 1) < δ)) ∪
            ((Finset.Icc (max 2 (m + 1)) (kA - 1)).filter
              (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
                sA i - sA (i - 1) < δ)) := by
          intro i hi
          obtain ⟨hiI, hpw⟩ := Finset.mem_filter.mp hi
          obtain ⟨hi2, hiK⟩ := Finset.mem_Icc.mp hiI
          by_cases hc : i ≤ m
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi2, hc⟩, hpw⟩)
          · exact Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hiK⟩, hpw⟩)
        rcases Finset.eq_empty_or_nonempty ((Finset.Icc 2 m).filter
            (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
              sA i - sA (i - 1) < δ)) with hTe | hTn
        · -- no tail edge is counted: the head bound already covers everything
          refine le_trans (Finset.card_le_card ?_) hHbound
          intro i hi
          have hu := hsubF hi
          rw [hTe] at hu
          simpa using hu
        rcases Finset.eq_empty_or_nonempty ((Finset.Icc (max 2 (m + 1)) (kA - 1)).filter
            (fun i => c1 + sA 1 ≤ sA (i - 1) ∧ sA i ≤ c2 + sA 1 ∧
              sA i - sA (i - 1) < δ)) with hHe | hHn
        · -- no head edge is counted: the tail bound already covers everything
          refine le_trans (Finset.card_le_card ?_) hTbound
          intro i hi
          have hu := hsubF hi
          rw [hHe] at hu
          simpa using hu
        -- both stretches genuinely contribute: the pulled-back window of `γ` wraps
        obtain ⟨iT, hiT⟩ := hTn
        obtain ⟨iH, hiH⟩ := hHn
        obtain ⟨hiTI, hiTa, hiTb, -⟩ := Finset.mem_filter.mp hiT
        obtain ⟨hiT2, hiTm⟩ := Finset.mem_Icc.mp hiTI
        obtain ⟨hiHI, hiHa, hiHb, -⟩ := Finset.mem_filter.mp hiH
        obtain ⟨hiH2, hiHK⟩ := Finset.mem_Icc.mp hiHI
        have hbeta : (0:ℝ) ≤ c2 + sA 1 - (γ.len - t) := by
          obtain ⟨pH, qH⟩ := hhead iH (by omega) hiHK
          have h0 : (0:ℝ) ≤ s (iH - m) := hslow _ pH
          rw [qH] at hiHb
          linarith
        have halpha : c1 + sA 1 - (-t) ≤ γ.len := by
          obtain ⟨pT, qT⟩ := htail (iT - 1) (by omega) (by omega)
          have h0 : s (j0 + (iT - 1 - 1)) ≤ γ.len := hshigh _ pT
          rw [qT] at hiTa
          linarith
        refine SplicedBreakpointShortEdgeCount k n kA j0 m δ (-t) (γ.len - t)
          (c1 + sA 1) (c2 + sA 1) s sA hmonoS hs0 (by omega) (by omega) ?_ ?_ ?_ ?_ ?_
        · intro i hi1 hi2
          obtain ⟨pp, qq⟩ := htail i hi1 hi2
          exact ⟨pp, by rw [qq]; ring⟩
        · intro i hi1 hi2
          obtain ⟨pp, qq⟩ := hhead i hi1 hi2
          exact ⟨pp, by rw [qq]; ring⟩
        · rw [hsplice (by omega)]; ring
        · linarith
        · exact hwrap (c1 + sA 1 - (-t)) (c2 + sA 1 - (γ.len - t)) hbeta (by linarith) halpha
            (by linarith)
    -- reindex `j ↦ i = j + 1` from the sub-window's resolution to `sA`'s own indices
    refine le_trans (Finset.card_le_card_of_injOn (fun j => j + 1) ?_ ?_) hmain
    · intro j hj
      obtain ⟨hjI, hja, hjb, hjd⟩ := Finset.mem_filter.mp hj
      obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjI
      have e1 : 1 + (j - 1) = j := by omega
      have e3 : 1 + j = j + 1 := by omega
      rw [e1, e3] at hjd
      rw [e1] at hja
      rw [e3] at hjb
      have e2 : j + 1 - 1 = j := by omega
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by show 2 ≤ j + 1; omega, by show j + 1 ≤ kA - 1; omega⟩, ?_, ?_, ?_⟩
      · rw [e2]; linarith
      · linarith
      · rw [e2]; linarith
    · intro x hx y hy hxy
      have hxy' : x + 1 = y + 1 := hxy
      omega
  refine ⟨kA - 1 - 1, fun j => sA (1 + j) - sA 1,
    RestrictPiecewiseGeodesic (curveArc γ hcl t t' ht0 htl ht'0 ht'l) kA sA hresA 1 (kA - 1)
      (by omega) (by omega) h1 h1k hkl, ?_, ?_⟩
  · intro c1 c2 hc1 hc12 hc2len hgap
    exact key c1 c2 hc1 hc12 hc2len hgap
  · intro hclosed
    exact absurd hclosed hnc
