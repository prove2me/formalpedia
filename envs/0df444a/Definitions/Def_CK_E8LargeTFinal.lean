-- Prove2me | Definitions.Def_CK_E8LargeTFinal
-- name    : CK_E8LargeTFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:57:13.088214+00:00
-- url     : https://prove2.me/theorems/e530f5db-904c-4199-9e7e-ea8baecc77a2
-- title:
--   Courtade–Kumar proof module `E8LargeTFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8LargeTFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8LargeTFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8LargeTFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8LargeTFinal.lean)

import Definitions.Def_CK_E8TightArgumentJets
import Definitions.Def_CK_E8TailElevenNineDerivatives

-- ===== source module E8LargeTFinal =====
section

namespace GeneralCK.E8LargeTSAxis

open Set

set_option maxHeartbeats 1000000

theorem relative_upper_shift_elevenNine {t z : ℝ} (ht : 119/10 ≤ t) (htz : t ≤ z)
    (hz : z ∈ e8SlopeRange) (hwidth : z-t ≤ 1/4) :
    e8RegularQ z ≤ 5/4*e8RegularQ t := by
  have hrange (u : ℝ) (hu : u ∈ Icc t z) : u ∈ e8SlopeRange :=
    e8SlopeRange_downward hz (by linarith [hu.1]) hu.2
  let g : ℝ → ℝ := fun u => 3/4*e8RegularQ z*u-e8RegularQ u
  have hd (u : ℝ) (hu : u ∈ Icc t z) :
      HasDerivAt g (3/4*e8RegularQ z-deriv e8RegularQ u) u := by
    have hq := (e8RegularQ_contDiffAt_of_mem (hrange u hu)).differentiableAt (by norm_num)
    convert! ((hasDerivAt_id u).const_mul (3/4*e8RegularQ z)).sub hq.hasDerivAt using 1
    simp
  have hg : MonotoneOn g (Icc t z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t z)
    · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
    · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Icc t z := interior_subset hu
      rw [(hd u hu').deriv]
      have hm := e8RegularQ_mono_of_mem (hrange u hu') hz hu'.2
      linarith [(inverse_first_bounds (hrange u hu') (by linarith [hu'.1])).2]
  have hgap := hg ⟨le_rfl, htz⟩ ⟨htz, le_rfl⟩ htz
  have hp := inverse_value hz (ht.trans htz)
  have htp := inverse_value (hrange t ⟨le_rfl, htz⟩) ht
  have hw := mul_nonneg (show 0 ≤ e8RegularQ z by linarith) (sub_nonneg.mpr hwidth)
  dsimp [g] at hgap
  nlinarith

theorem relative_lower_shift_elevenNine {t z : ℝ} (ht : 119/10 ≤ t) (htz : t ≤ z)
    (hz : z ∈ e8SlopeRange) :
    e8RegularQ t + 3/5*e8RegularQ t*(z-t) ≤ e8RegularQ z := by
  have hrange (u : ℝ) (hu : u ∈ Icc t z) : u ∈ e8SlopeRange :=
    e8SlopeRange_downward hz (by linarith [hu.1]) hu.2
  let g : ℝ → ℝ := fun u => e8RegularQ u-3/5*e8RegularQ t*u
  have hd (u : ℝ) (hu : u ∈ Icc t z) :
      HasDerivAt g (deriv e8RegularQ u-3/5*e8RegularQ t) u := by
    have hq := (e8RegularQ_contDiffAt_of_mem (hrange u hu)).differentiableAt (by norm_num)
    convert! hq.hasDerivAt.sub ((hasDerivAt_id u).const_mul (3/5*e8RegularQ t)) using 1
    simp
  have hg : MonotoneOn g (Icc t z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t z)
    · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
    · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Icc t z := interior_subset hu
      rw [(hd u hu').deriv]
      have hm := e8RegularQ_mono_of_mem (hrange t ⟨le_rfl, htz⟩) (hrange u hu') hu'.1
      linarith [(inverse_first_bounds (hrange u hu') (by linarith [hu'.1])).1]
  have hgap := hg ⟨le_rfl, htz⟩ ⟨htz, le_rfl⟩ htz
  dsimp [g] at hgap
  linarith

theorem secondSJet_positive_elevenNine {A B C D B1 C1 D1 B2 C2 D2 : ℝ}
    (hA : 40 ≤ A) (hAB : A ≤ B) (hAC : A ≤ C)
    (hD : D ≤ 1/2) (hD1 : D1 ≤ 1/5) (hD2 : D2 ≤ 1/10)
    (hB1l : 3/5*B ≤ B1) (hB1u : B1 ≤ 3/4*B) (hC1l : 3/5*C ≤ C1)
    (hB2l : 0 ≤ B2) (hB2u : B2 ≤ 1/2*B) (hC2l : 37/100*C ≤ C2)
    (hcases : B ≤ 5/4*A ∨ 43/40*A ≤ C) :
    0 < e8SecondSJet A B C D B1 C1 D1 B2 C2 D2 := by
  have hAp : 0 ≤ A := by linarith
  have hBp : 0 ≤ B := by linarith
  have hCp : 0 ≤ C := by linarith
  have hB1p : 0 ≤ B1 := by linarith
  have hC2p : 0 ≤ C2 := by linarith
  have hp := mul_le_mul hB1l hC1l (by positivity : (0 : ℝ) ≤ 3/5*C) hB1p
  have he1 := mul_le_mul_of_nonneg_left hD1 hB1p
  have he4 := mul_le_mul_of_nonpos_right hD2 (show A-B ≤ 0 by linarith)
  have hp2 := mul_le_mul_of_nonneg_right hC2l (show 0 ≤ A+B by linarith)
  have hBC := mul_le_mul_of_nonneg_left hAC hBp
  have hAC2 := mul_le_mul_of_nonneg_left hAC hAp
  rcases hcases with hsmall | hlarge
  · have he2 := mul_le_mul_of_nonneg_left (show -(A+1/2) ≤ C-2*A-D by linarith) hB2l
    have he3 := mul_le_mul_of_nonneg_right hB2u (show 0 ≤ A+1/2 by linarith)
    have hAB2 := mul_le_mul_of_nonneg_left hsmall hAp
    have hmargin := mul_nonneg (show 0 ≤ A-40 by linarith) hAp
    unfold e8SecondSJet
    nlinarith only [hp, he1, he4, hp2, hBC, hAC2, he2, he3, hAB2,
      hmargin, hA, hsmall, hB1u]
  · by_cases hsign : 0 ≤ C-2*A-D
    · have he2 := mul_nonneg hB2l hsign
      have hmargin := mul_nonneg (show 0 ≤ A-40 by linarith) hBp
      unfold e8SecondSJet
      nlinarith only [hp, he1, he4, hp2, hBC, hAC2, he2, hmargin,
        hA, hAB, hB1u]
    · have he2 := mul_le_mul_of_nonpos_right hB2u (le_of_not_ge hsign)
      have he3 := mul_le_mul_of_nonneg_left hD hBp
      have hBC2 := mul_le_mul_of_nonneg_left hlarge hBp
      have hmargin := mul_nonneg (show 0 ≤ A-40 by linarith) hBp
      unfold e8SecondSJet
      nlinarith only [hp, he1, he4, hp2, he2, he3, hBC2, hAC2,
        hmargin, hA, hAB, hB1u]

theorem largeT_elevenNine_secondS {s t : ℝ} (hadm : E8Admissible s t)
    (hs : s ≤ 63/20) (ht : 119/10 ≤ t) : 0 < e8RegularDeltaSS s t := by
  have hd := bounded_argument_jets_tight hadm.2.2.1 hs
  have hA := inverse_value hadm.2.2.2.1 ht
  have hAB := e8RegularQ_mono_of_mem hadm.2.2.2.1 hadm.2.2.2.2.2 (by linarith [hadm.1])
  have hAC := e8RegularQ_mono_of_mem hadm.2.2.2.1 hadm.2.2.2.2.1 (by linarith [hadm.1])
  have hB1 := inverse_first_bounds hadm.2.2.2.2.2 (by linarith [hadm.1])
  have hC1 := inverse_first_bounds hadm.2.2.2.2.1 (by linarith [hadm.1])
  have hB2 := inverse_second_bounds hadm.2.2.2.2.2 (by linarith [hadm.1])
  have hC2 := inverse_second_bounds hadm.2.2.2.2.1 (by linarith [hadm.1])
  rw [e8RegularDeltaSS_eq_jet hadm]
  apply secondSJet_positive_elevenNine hA hAB hAC hd.1 hd.2.1 hd.2.2
    hB1.1 hB1.2 hC1.1 (by linarith) hB2.2 hC2.1
  by_cases hsmall : s ≤ 1/8
  · exact Or.inl (relative_upper_shift_elevenNine ht (by linarith [hadm.1]) hadm.2.2.2.2.2 (by linarith))
  · right
    have hh := relative_lower_shift_elevenNine ht (show t ≤ s+t by linarith [hadm.1]) hadm.2.2.2.2.1
    have hp := mul_nonneg (show 0 ≤ e8RegularQ t by linarith) (show 0 ≤ s-1/8 by linarith)
    nlinarith only [hh, hp]

theorem largeT_elevenNine : E8PositiveOn (fun s t => 119/10 ≤ t ∧ s ≤ 63/20) := by
  intro s t hadm hr
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact largeT_elevenNine_secondS (hadm.mono_s hu.1 hu.2.le) (hu.2.le.trans hr.2) hr.1

theorem largeT : E8PositiveOn (fun s t =>
    (119/10 : ℝ) ≤ t ∧ (1/200 : ℝ) ≤ s ∧ s ≤ 63/20) := by
  intro s t hadm hr
  exact largeT_elevenNine s t hadm ⟨hr.1, hr.2.2⟩

#print axioms relative_upper_shift_elevenNine
#print axioms relative_lower_shift_elevenNine
#print axioms secondSJet_positive_elevenNine
#print axioms largeT_elevenNine_secondS
#print axioms largeT_elevenNine
#print axioms largeT

end GeneralCK.E8LargeTSAxis

end


