-- Prove2me | solution 1 for AlmostPeriodic.upperDensity_pos_of_isAlmostPeriodicOnStrip
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:45:23.945825+00:00
-- url     : https://prove2.me/submissions/281d639b-b7a4-434a-9544-f42fd2388d93

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm
import Definitions.Def_AlmostPeriodic_AnalyticStrip

open Filter Topology Set MeasureTheory AlmostPeriodic

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem density_of_regular_intervals (X : Set ℝ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hCover : ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), Icc τ (τ + r) ⊆ X) :
    0 < MasulloGRH.upperDensity X := by
  let H := L + r + 1
  have hH : 0 < H := by dsimp [H]; linarith
  choose τ hτ hX using fun j : ℕ => hCover ((j : ℝ) * H)
  have hSep (i j : ℕ) (hij : i < j) : τ i + r < τ j := by
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hmul := mul_le_mul_of_nonneg_right hcast hH.le
    have hi := (hτ i).2
    have hj := (hτ j).1
    change τ i ≤ (i : ℝ) * H + L at hi
    change (j : ℝ) * H ≤ τ j at hj
    have hLen : L + r < H := by dsimp [H]; linarith
    linarith only [hi, hj, hmul, hLen]
  have hRatio (n : ℕ) (hn : 0 < n) :
      r / (2 * H) ≤ volume.real (Icc (-((n : ℝ) * H)) ((n : ℝ) * H) ∩ X) /
        (2 * ((n : ℝ) * H)) := by
    let T := (n : ℝ) * H
    have hT : 0 < T := mul_pos (by exact_mod_cast hn) hH
    let I (j : ℕ) := Icc (τ j) (τ j + r)
    have hDis : PairwiseDisjoint (↑(Finset.range n) : Set ℕ) I := by
      intro i _ j _ hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact Set.disjoint_left.mpr fun z hz hz' => (hSep i j h).not_ge (hz'.1.trans hz.2)
      · exact Set.disjoint_left.mpr fun z hz hz' => (hSep j i h).not_ge (hz.1.trans hz'.2)
    have hSubset : (⋃ j ∈ Finset.range n, I j) ⊆ Icc (-T) T ∩ X := by
      intro z hz
      rw [mem_iUnion₂] at hz
      obtain ⟨j, hj, hz⟩ := hz
      have h0 : 0 ≤ τ j := (mul_nonneg (Nat.cast_nonneg j) hH.le).trans (hτ j).1
      have hTop : τ j + r ≤ T := by
        have hcast : (j : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        have hmul := mul_le_mul_of_nonneg_right hcast hH.le
        have hUp := (hτ j).2
        change τ j ≤ (j : ℝ) * H + L at hUp
        have hLen : L + r < H := by dsimp [H]; linarith
        dsimp only [T]
        linarith only [hUp, hmul, hLen]
      exact ⟨⟨by linarith [hz.1], hz.2.trans hTop⟩, hX j hz⟩
    have hMass : (n : ℝ) * r ≤ volume.real (Icc (-T) T ∩ X) := by
      calc
        (n : ℝ) * r = volume.real (⋃ j ∈ Finset.range n, I j) := by
          rw [measureReal_biUnion_finset hDis (fun j _ => measurableSet_Icc)
            (fun j _ => by simp [I, Real.volume_Icc])]
          simp [I, Real.volume_real_Icc, hr.le]
        _ ≤ _ := measureReal_mono hSubset
          (measure_ne_top_of_subset inter_subset_left (by simp [Real.volume_Icc]))
    apply (le_div_iff₀ (mul_pos (by norm_num) hT)).mpr
    calc
      r / (2 * H) * (2 * T) = (n : ℝ) * r := by dsimp only [T]; field_simp
      _ ≤ _ := hMass
  let q (T : ℝ) := volume.real (Icc (-T) T ∩ X) / (2 * T)
  have hBound : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) q := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).mpr
    have hh := measureReal_mono (μ := volume)
      (inter_subset_left : Icc (-T) T ∩ X ⊆ Icc (-T) T) (by simp [Real.volume_Icc])
    rw [Real.volume_real_Icc_of_le (by linarith)] at hh
    linarith
  have hOften : ∃ᶠ T in atTop, r / (2 * H) ≤ q T := by
    refine frequently_atTop.mpr fun a => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (a / H))
    have hn0 : 0 < n := by exact_mod_cast (le_max_left _ _).trans_lt hn
    have ha : a ≤ (n : ℝ) * H :=
      (div_le_iff₀ hH).mp ((le_max_right _ _).trans hn.le)
    exact ⟨(n : ℝ) * H, ha, hRatio n hn0⟩
  exact (div_pos hr (by positivity : 0 < 2 * H)).trans_le
    (le_limsup_of_frequently_le hOften hBound)

theorem solution (f : ℂ → ℂ) (a b : ℝ) (hf : IsAlmostPeriodicOnStrip f a b)
    (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ {s : ℂ | a < s.re ∧ s.re < b})
    (ε : ℝ) (hε : 0 < ε) :
    0 < MasulloGRH.upperDensity
      {t : ℝ | sSup ((fun s : ℂ => ‖f (s + (t : ℂ) * Complex.I) - f s‖) '' K) < ε} := by
  let X := {t : ℝ | sSup ((fun s : ℂ => ‖f (s + (t : ℂ) * Complex.I) - f s‖) '' K) < ε}
  rcases K.eq_empty_or_nonempty with hEmpty | hNon
  · apply density_of_regular_intervals X 1 1 zero_lt_one zero_lt_one
    intro c
    refine ⟨c, ⟨le_rfl, by linarith⟩, fun t _ => ?_⟩
    simpa [X, hEmpty] using hε
  · obtain ⟨x, hx, hMin⟩ := hK.exists_isMinOn hNon Complex.continuous_re.continuousOn
    obtain ⟨y, hy, hMax⟩ := hK.exists_isMaxOn hNon Complex.continuous_re.continuousOn
    obtain ⟨L, hL, hAlmost⟩ := hf.2 x.re y.re (hKs hx).1 (hKs hy).2
      (ε / 4) (by linarith)
    let shift (p : ℂ × ℝ) := p.1 + (p.2 : ℂ) * Complex.I
    have hRe (s : ℂ) (t : ℝ) : (shift (s, t)).re = s.re := by simp [shift, Complex.mul_re]
    let K' := shift '' (K ×ˢ Icc (-1 : ℝ) 1)
    have hK' : IsCompact K' := (hK.prod isCompact_Icc).image (by unfold shift; fun_prop)
    have hK's : K' ⊆ {s : ℂ | a < s.re ∧ s.re < b} := by
      rintro _ ⟨⟨s, t⟩, hs, rfl⟩
      simpa only [mem_ofPred_eq, hRe] using hKs hs.1
    obtain ⟨δ, hδ, hδclose⟩ := Metric.uniformContinuousOn_iff.mp
      (hK'.uniformContinuousOn_of_continuous (hf.1.continuousOn.mono hK's))
      (ε / 4) (by linarith)
    let r := min 1 (δ / 2)
    have hr : 0 < r := lt_min zero_lt_one (half_pos hδ)
    apply density_of_regular_intervals X L r hL hr
    intro c
    obtain ⟨τ, hτ, hτc⟩ := hAlmost c
    refine ⟨τ, hτc, fun t ht => ?_⟩
    have hh : t - τ ∈ Icc (0 : ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hh' : t - τ ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hh.1], hh.2.trans (min_le_left _ _)⟩
    change sSup ((fun s : ℂ => ‖f (s + (t : ℂ) * Complex.I) - f s‖) '' K) < ε
    refine (csSup_le (hNon.image _) ?_).trans_lt (show ε / 2 < ε by linarith)
    rintro _ ⟨s, hs, rfl⟩
    let z := shift (s, t - τ)
    have hz : z ∈ K' := ⟨(s, t - τ), ⟨hs, hh'⟩, rfl⟩
    have hs' : s ∈ K' := ⟨(s, 0), ⟨hs, by norm_num⟩, by simp [shift]⟩
    have hd : dist z s < δ := by
      rw [dist_eq_norm]
      have hsz : z - s = ((t - τ : ℝ) : ℂ) * Complex.I := by dsimp only [z, shift]; ring
      rw [hsz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hh.1]
      exact hh.2.trans_lt ((min_le_right _ _).trans_lt (by linarith))
    have hSmall := hδclose z hz s hs' hd
    rw [dist_eq_norm] at hSmall
    have hShift : z + (τ : ℂ) * Complex.I = s + (t : ℂ) * Complex.I := by
      dsimp [z, shift]
      push_cast
      ring
    have hτ' := hτ z (by rw [hRe]; exact hMin hs) (by rw [hRe]; exact hMax hs)
    rw [hShift] at hτ'
    exact (norm_sub_le_norm_sub_add_norm_sub _ (f z) _).trans (by linarith)
