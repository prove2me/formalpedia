-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexFixedPoint
-- name    : CK_GeneralCK_ReflectionComplexFixedPoint
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:42:13.37982+00:00
-- url     : https://prove2.me/theorems/22dd8936-7955-4cb2-bc8e-85f34fa2af9d
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexFixedPoint` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexFixedPoint` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexFixedPoint` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexFixedPoint (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexFixedPoint.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexEntropy
import Mathlib.Topology.MetricSpace.Contracting

-- ===== source module GeneralCK.ReflectionComplexFixedPoint =====
section

/-!
# Fixed contact point on the complex small-bias disc

This file applies the Banach contraction theorem to the verified complex
entropy map.  It also records conjugation symmetry, so real parameters have a
real fixed contact point.
-/

namespace GeneralCK.Reflection.ComplexFixedPoint

open Set Function
open ComplexEntropy
open scoped ComplexConjugate

private abbrev contactDisc : Set ℂ := Metric.closedBall 0 (4 / 5 : ℝ)

private noncomputable abbrev contact (tau : ℂ) : ℂ → ℂ :=
  ComplexDiscElementary.contactMap entropyExt tau

private theorem contact_mapsTo {tau : ℂ} (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    MapsTo (contact tau) contactDisc contactDisc :=
  (entropyContactMap_contractionPackage htau).1

private theorem contact_contracting_restrict {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    ContractingWith (49 / 50 : NNReal)
      ((contact_mapsTo htau).restrict (contact tau) contactDisc contactDisc) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro c d
  exact (entropyContactMap_lipschitzOnWith htau).dist_le_mul c c.property d d.property

/-- The entropy contact equation has exactly one solution in the closed
`4/5` disc.  That solution actually lies in the open disc. -/
theorem exists_unique_fixedPoint {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    ∃! c : ℂ, c ∈ Metric.ball 0 (4 / 5 : ℝ) ∧ IsFixedPt (contact tau) c := by
  have hcomplete : IsComplete contactDisc := Metric.isClosed_closedBall.isComplete
  have hzero : (0 : ℂ) ∈ contactDisc := by
    simp only [contactDisc, Metric.mem_closedBall, dist_self]
    norm_num
  have hfinite := edist_ne_top (0 : ℂ) (contact tau 0)
  rcases (contact_contracting_restrict htau).exists_fixedPoint'
      hcomplete (contact_mapsTo htau) hzero hfinite with
    ⟨c, hc, hfix, _hlim, _herror⟩
  have hcOpen : c ∈ Metric.ball 0 (4 / 5 : ℝ) := by
    have himage := entropyContactMap_mapsTo_ball htau hc
    simpa only [hfix.eq] using himage
  refine ⟨c, ⟨hcOpen, hfix⟩, ?_⟩
  intro d hd
  exact ComplexDiscElementary.fixedPoint_unique
    (entropyContactMap_lipschitzOnWith htau)
    (Metric.ball_subset_closedBall hd.1) hc hd.2 hfix

/-- A convenient chosen version of the unique contact point. -/
noncomputable def fixedPoint (tau : ℂ) (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) : ℂ :=
  Classical.choose (exists_unique_fixedPoint htau).exists

theorem fixedPoint_mem_ball {tau : ℂ} (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    fixedPoint tau htau ∈ Metric.ball 0 (4 / 5 : ℝ) :=
  (Classical.choose_spec (exists_unique_fixedPoint htau).exists).1

theorem fixedPoint_isFixedPt {tau : ℂ} (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) :
    IsFixedPt (contact tau) (fixedPoint tau htau) :=
  (Classical.choose_spec (exists_unique_fixedPoint htau).exists).2

theorem eq_fixedPoint {tau c : ℂ} (htau : ‖tau‖ ≤ (7 / 10 : ℝ))
    (hc : c ∈ Metric.closedBall 0 (4 / 5 : ℝ)) (hfix : IsFixedPt (contact tau) c) :
    c = fixedPoint tau htau :=
  ComplexDiscElementary.fixedPoint_unique
    (entropyContactMap_lipschitzOnWith htau) hc
    (Metric.ball_subset_closedBall (fixedPoint_mem_ball htau)) hfix
    (fixedPoint_isFixedPt htau)

/-- The principal-log entropy extension commutes with complex conjugation on
the open unit disc. -/
theorem entropyExt_conj {c : ℂ} (hc : ‖c‖ < 1) :
    entropyExt (conj c) = conj (entropyExt c) := by
  have hp := Complex.log_conj (1 + c)
    (Complex.slitPlane_arg_ne_pi (Complex.mem_slitPlane_of_norm_lt_one hc))
  have hm := Complex.log_conj (1 - c)
    (Complex.slitPlane_arg_ne_pi (by
      simpa only [sub_eq_add_neg, norm_neg] using
        (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc))))
  unfold entropyExt
  rw [show 1 + conj c = conj (1 + c) by simp,
    show 1 - conj c = conj (1 - c) by simp, hp, hm]
  simp only [map_sub, map_add, map_mul, div_eq_mul_inv, map_inv₀,
    Complex.conj_ofReal, map_ofNat]

/-- For a real parameter, every fixed point in the contact disc is real. -/
theorem fixedPoint_im_eq_zero {tau c : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) (htauReal : tau.im = 0)
    (hc : c ∈ Metric.closedBall 0 (4 / 5 : ℝ))
    (hfix : IsFixedPt (contact tau) c) : c.im = 0 := by
  have htauConj : conj tau = tau := Complex.conj_eq_iff_im.mpr htauReal
  have hcNorm : ‖c‖ < 1 := by
    have : ‖c‖ ≤ (4 / 5 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hc
    exact this.trans_lt (by norm_num)
  have hconjFix : IsFixedPt (contact tau) (conj c) := by
    unfold IsFixedPt contact ComplexDiscElementary.contactMap at hfix ⊢
    rw [entropyExt_conj hcNorm]
    calc
      tau * conj (entropyExt c) = conj tau * conj (entropyExt c) := by rw [htauConj]
      _ = conj (tau * entropyExt c) := (map_mul (starRingEnd ℂ) _ _).symm
      _ = conj c := congrArg (starRingEnd ℂ) hfix
  have hconjMem : conj c ∈ Metric.closedBall 0 (4 / 5 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hc
  have heq : conj c = c := ComplexDiscElementary.fixedPoint_unique
    (entropyContactMap_lipschitzOnWith htau) hconjMem hc hconjFix hfix
  exact Complex.conj_eq_iff_im.mp heq

theorem chosen_fixedPoint_im_eq_zero {tau : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ)) (htauReal : tau.im = 0) :
    (fixedPoint tau htau).im = 0 :=
  fixedPoint_im_eq_zero htau htauReal
    (Metric.ball_subset_closedBall (fixedPoint_mem_ball htau)) (fixedPoint_isFixedPt htau)

/-- Stability of contact points with respect to the complex parameter.  The
constant is `(1103/1000) / (1 - 49/50) = 1103/20`. -/
theorem fixedPoint_dist_le {tau sigma c d : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ))
    (hc : c ∈ Metric.closedBall 0 (4 / 5 : ℝ))
    (hd : d ∈ Metric.closedBall 0 (4 / 5 : ℝ))
    (hcfix : IsFixedPt (contact tau) c)
    (hdfix : IsFixedPt (contact sigma) d) :
    dist c d ≤ (1103 / 20 : ℝ) * dist tau sigma := by
  have hcontract : dist (contact tau c) (contact tau d) ≤
      (49 / 50 : ℝ) * dist c d :=
    (entropyContactMap_lipschitzOnWith htau).dist_le_mul c hc d hd
  have hparameter : dist (contact tau d) (contact sigma d) ≤
      (1103 / 1000 : ℝ) * dist tau sigma := by
    simp only [contact, ComplexDiscElementary.contactMap, dist_eq_norm]
    rw [← sub_mul, Complex.norm_mul]
    calc
      ‖tau - sigma‖ * ‖entropyExt d‖ ≤
          ‖tau - sigma‖ * (1103 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_left (entropyExt_uniformBound d hd) (norm_nonneg _)
      _ = (1103 / 1000 : ℝ) * ‖tau - sigma‖ := by ring
  have htriangle : dist c d ≤
      (49 / 50 : ℝ) * dist c d +
        (1103 / 1000 : ℝ) * dist tau sigma := by
    calc
      dist c d = dist (contact tau c) (contact sigma d) := by
        rw [hcfix.eq, hdfix.eq]
      _ ≤ dist (contact tau c) (contact tau d) +
          dist (contact tau d) (contact sigma d) := dist_triangle _ _ _
      _ ≤ _ := add_le_add hcontract hparameter
  nlinarith [show 0 ≤ dist tau sigma from dist_nonneg]

theorem chosen_fixedPoint_dist_le {tau sigma : ℂ}
    (htau : ‖tau‖ ≤ (7 / 10 : ℝ))
    (hsigma : ‖sigma‖ ≤ (7 / 10 : ℝ)) :
    dist (fixedPoint tau htau) (fixedPoint sigma hsigma) ≤
      (1103 / 20 : ℝ) * dist tau sigma :=
  fixedPoint_dist_le htau
    (Metric.ball_subset_closedBall (fixedPoint_mem_ball htau))
    (Metric.ball_subset_closedBall (fixedPoint_mem_ball hsigma))
    (fixedPoint_isFixedPt htau) (fixedPoint_isFixedPt hsigma)

end GeneralCK.Reflection.ComplexFixedPoint

end


