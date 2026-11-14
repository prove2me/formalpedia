-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualConstructor
-- name    : ConsistentSubmodular_Deterministic_Certificates_ActualConstructor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:24.17087+00:00
-- url     : https://prove2.me/theorems/3cd4a6ea-c86e-46a2-9d26-7e820eec81bf
-- title:
--   Actual-coverage constructor on atomic profiles: active stages, envelope slack, actual and sufficient eligibility
-- statement:
--   Let $P$ be an atomic profile with stages $0,\dots,m$, with baseline $L_t$ (`baseline`), residuals $r_{i,t}$ (`residual`), designated mass $A_t=r_{t,t}$ (`designated`), benchmark $B_t=L_t+A_t$ (`benchmark`), and mixture value $V_t(p)$ (`value`). The file defines, for stages $h,c,t$ and a mass parameter $q\in\mathbb R$:
--
--   - `Active`: stage $t$ is active if $L_t<3A_t$, i.e. the baseline alone does not already meet the $3/4$ level.
--   - `envelopeSlack` $h\,q\,t$:
--   $$q\big((A_h-A_t)+(A_t-r_{h,t})\big)+(B_t-A_h)+3(1-A_h)-4(A_t-r_{h,t}).$$
--   A nonnegative value at an active stage $t$ is the envelope condition on $q$.
--   - `actualEligibility` $h\,q\,c$:
--   $$4A_h-3-q(A_h-A_c)-\Big(q-\tfrac{q^2}{4}\Big)r_{h,c}.$$
--   A candidate partner $c$ is eligible when this is nonnegative; the last eligible partner is selected.
--   - `suffEligibility` $h\,q\,c$:
--   $$(A_c-r_{h,c})-(q-1)(A_h-A_c)-3(1-A_h),$$
--   the corresponding test for the minimum-overlap sufficient exit.
--
--   The constructor uses the point $\mathrm{mix}(\delta_h,\delta_c,q/4)$ of the simplex, a mixture of two vertices. The file also proves that the envelope slack is nonnegative for $t\le h$ (under canonicity), the prefix, suffix and entry-edge inequalities for such a pair, and the theorems `actual_constructor_stages` and `actual_low_constructor_stages`, which show that if $h<c$, the envelope holds on later active stages and eligibility fails after $c$, then $\tfrac34B_t\le V_t(\mathrm{mix}(\delta_h,\delta_c,q/4))$ for all $t$, for $1\le q\le 2$ and for a low positive envelope $q\le 1$ respectively.
--
--   These definitions drive the construction of two-support checkpoints in the deterministic $3/4$ certificate argument (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ActualConstructor.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicFacts
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SafePaths
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ConstructorScalar

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

def Active (t : Fin (m + 1)) : Prop := P.baseline t < 3 * P.designated t

def envelopeSlack (h : Fin (m + 1)) (q : ℝ) (t : Fin (m + 1)) : ℝ :=
  q * ((P.designated h - P.designated t) + (P.designated t - P.residual h t)) +
    (P.benchmark t - P.designated h) + 3 * (1 - P.designated h) -
      4 * (P.designated t - P.residual h t)

def actualEligibility (h : Fin (m + 1)) (q : ℝ) (c : Fin (m + 1)) : ℝ :=
  4 * P.designated h - 3 - q * (P.designated h - P.designated c) -
    (q - q ^ 2 / 4) * P.residual h c

def suffEligibility (h : Fin (m + 1)) (q : ℝ) (c : Fin (m + 1)) : ℝ :=
  (P.designated c - P.residual h c) - (q - 1) * (P.designated h - P.designated c) -
    3 * (1 - P.designated h)

theorem envelopeSlack_early (hP : P.Canonical) (h t : Fin (m + 1))
    (q : ℝ) (hth : t ≤ h) : 0 ≤ P.envelopeSlack h q t := by
  unfold envelopeSlack benchmark
  rw [P.residual_persistence h t hth]
  have := P.designated_le_one hP t
  have := P.baseline_nonnegative t
  nlinarith

theorem actual_pair_prefix (h c t : Fin (m + 1)) (hc : h ≠ c)
    (q : ℝ) (hq0 : 0 ≤ q) (hq4 : q ≤ 4) (htc : t ≤ c)
    (helig : 0 ≤ P.actualEligibility h q c)
    (henv : 0 ≤ P.envelopeSlack h q t) :
    (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  have hlow := P.value_mix_vertices_lower t h c hc
    (show 0 ≤ q / 4 by positivity) (show q / 4 ≤ 1 by linarith)
    (P.overlap_le_persistent h c t)
  rw [P.residual_persistence c t htc] at hlow
  have hs := actual_prefix_margin (P.designated h) q (P.baseline t)
    (P.designated t) (P.residual h t) (P.designated c) (P.residual h c)
    helig henv
  exact hs.trans hlow

theorem actual_pair_entry (hP : P.Canonical) (h c : Fin (m + 1)) (hhc : h < c)
    (q : ℝ) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (helig : 0 ≤ P.actualEligibility h q c) :
    SafePath P 0 ((3 : ℝ) / 4)
      (PolygonalPath.segment (vertex h) (mix (vertex h) (vertex c) (q / 4))) := by
  apply safePath_segment
  intro y hy hy1
  have hmix : mix (vertex h) (mix (vertex h) (vertex c) (q / 4)) y =
      mix (vertex h) (vertex c) (y * (q / 4)) := by
    funext i
    simp only [mix]
    ring
  rw [hmix]
  have hx : 0 ≤ y * (q / 4) := by positivity
  have hxx : y * (q / 4) ≤ q / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy1) hq0]
  have hx1 : y * (q / 4) ≤ 1 := by linarith
  refine ⟨(simplex_vertex h).mix (simplex_vertex c) hx hx1, ?_⟩
  have hlow := P.value_mix_vertices_lower 0 h c (ne_of_lt hhc) hx hx1
    (P.overlap_le_persistent h c 0)
  rw [P.baseline_zero, P.residual_persistence h 0 (Fin.zero_le _),
    P.residual_persistence c 0 (Fin.zero_le _)] at hlow
  have hδ := sub_nonneg.mpr (P.designated_antitone hP (le_of_lt hhc))
  have hend : (3 : ℝ) / 4 ≤ P.designated h -
      (P.designated h - P.designated c) * (q / 4) -
        P.residual h c * (q / 4) * (1 - q / 4) := by
    unfold actualEligibility at helig
    nlinarith
  have hs := actual_entry_segment (P.designated h) (P.designated h - P.designated c)
    (P.residual h c) (q / 4) hδ (P.residual_nonnegative h c)
    (by linarith) hend (y * (q / 4)) hx hxx
  nlinarith

theorem actual_pair_suffix (_hP : P.Canonical) (h c t : Fin (m + 1)) (hc : h ≠ c)
    (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hct : c ≤ t)
    (hnoelig : P.actualEligibility h q t ≤ 0)
    (hcredit : 2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
      q * (P.benchmark c - P.designated h)) :
    (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  have hq0 : 0 < q := by linarith
  have hlow := P.value_mix_vertices_lower t h c hc
    (show 0 ≤ q / 4 by positivity) (show q / 4 ≤ 1 by linarith)
    (le_min (P.overlap_le_left h c t) (P.overlap_le_right h c t))
  have hpersist := P.baseline_add_residual_monotone c hct
  change P.benchmark c ≤ P.baseline t + P.residual c t at hpersist
  have hcross := actual_suffix_min_crossing q (P.residual h t) (P.residual c t) hq1 hq2
  have hno : (q - q ^ 2 / 4) * (P.designated t - P.residual h t) ≤
      (q - (q - q ^ 2 / 4)) * (P.designated h - P.designated t) +
        (q - q ^ 2 / 4) * P.designated h - (4 * P.designated h - 3) := by
    unfold actualEligibility at hnoelig
    nlinarith
  have hr := P.residual_nonnegative h t
  have hs := actual_suffix_credit (P.designated h) (4 * P.designated h - 3)
    q (q - q ^ 2 / 4) (P.designated h - P.designated t)
    (P.designated t - P.residual h t) (P.benchmark c - P.designated h)
    hq1 hq2 rfl hcredit hno (by linarith)
  unfold benchmark
  nlinarith

/-- Every row of the actual constructor, including all earlier rows and every
inactive stage. The hypotheses preserve the prescribed active-row scope. -/
theorem actual_constructor_stages (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (helig : 0 ≤ P.actualEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.actualEligibility h q t ≤ 0)
    (hcredit : 2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
      q * (P.benchmark c - P.designated h)) :
    ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  intro t
  by_cases ht : P.Active t
  · by_cases htc : t ≤ c
    · apply P.actual_pair_prefix h c t (ne_of_lt hhc) q (by linarith)
        (by linarith) htc helig
      by_cases hth : t ≤ h
      · exact P.envelopeSlack_early hP h t q hth
      · exact henv t (lt_of_not_ge hth) ht
    · exact P.actual_pair_suffix hP h c t (ne_of_lt hhc) q hq1 hq2
        (le_of_lt (lt_of_not_ge htc)) (hlast t (lt_of_not_ge htc) ht) hcredit
  · apply P.inactive_stage_safe t
      ((simplex_vertex h).mix (simplex_vertex c) (by positivity) (by linarith))
    exact le_of_not_gt ht

theorem actual_low_pair_suffix (hP : P.Canonical) (h c t : Fin (m + 1))
    (hc : h ≠ c) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hct : c ≤ t)
    (henv : 0 ≤ P.envelopeSlack h q c)
    (helig : 0 ≤ P.actualEligibility h q c)
    (hnoelig : P.actualEligibility h q t ≤ 0) :
    (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  have hlow := P.value_mix_vertices_lower t h c hc
    (show 0 ≤ q / 4 by positivity) (show q / 4 ≤ 1 by linarith)
    (le_min (P.overlap_le_left h c t) (P.overlap_le_right h c t))
  have hpersist := P.baseline_add_residual_monotone c hct
  change P.benchmark c ≤ P.baseline t + P.residual c t at hpersist
  obtain ⟨hm0, hm1⟩ := overlap_coefficient_bounds q hq (show q ≤ 2 by linarith)
  have hy : P.residual c t ≤ P.designated t := hP.2 t c
  have hyterm := mul_le_mul_of_nonpos_left hy (show q - 1 ≤ 0 by linarith)
  have hoterm := mul_le_mul_of_nonneg_left
    (min_le_left (P.residual h t) (P.residual c t)) (le_of_lt hm0)
  have helig' : 0 ≤ (4 * P.designated h - 3) - q * (P.designated h - P.designated c) -
      (q - q ^ 2 / 4) *
        (P.designated h - (P.designated h - P.designated c) -
          (P.designated c - P.residual h c)) := by
    unfold actualEligibility at helig
    nlinarith only [helig]
  have hnoelig' : (4 * P.designated h - 3) - q * (P.designated h - P.designated t) -
      (q - q ^ 2 / 4) *
        (P.designated h - (P.designated h - P.designated t) -
          (P.designated t - P.residual h t)) ≤ 0 := by
    unfold actualEligibility at hnoelig
    nlinarith only [hnoelig]
  have hs := actual_low_suffix (P.designated h) (4 * P.designated h - 3)
    (3 * (1 - P.designated h)) q (q - q ^ 2 / 4)
    (P.designated h - P.designated c) (P.designated c - P.residual h c)
    (P.benchmark c - P.designated h)
    (P.designated h - P.designated t) (P.designated t - P.residual h t)
    hq hq1 rfl (by ring) henv helig' hnoelig'
  unfold benchmark
  nlinarith

/-- A last eligible partner for a low positive envelope already supplies all
stage guarantees; there is no additional credit-test hypothesis. -/
theorem actual_low_constructor_stages (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (helig : 0 ≤ P.actualEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.actualEligibility h q t ≤ 0) :
    ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  intro t
  by_cases ht : P.Active t
  · by_cases htc : t ≤ c
    · apply P.actual_pair_prefix h c t (ne_of_lt hhc) q hq.le (by linarith) htc helig
      by_cases hth : t ≤ h
      · exact P.envelopeSlack_early hP h t q hth
      · exact henv t (lt_of_not_ge hth) ht
    · have hct : c < t := lt_of_not_ge htc
      exact P.actual_low_pair_suffix hP h c t (ne_of_lt hhc) q hq hq1 hct.le
        (henv c hhc (P.active_is_prefix hP hct.le ht)) helig (hlast t hct ht)
  · apply P.inactive_stage_safe t
      ((simplex_vertex h).mix (simplex_vertex c) (by positivity) (by linarith))
    exact le_of_not_gt ht

end AtomicProfile

end ConsistentSubmodular

end


