-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ConstructorScalar
-- name    : ConsistentSubmodular_Deterministic_Certificates_ConstructorScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:35.664616+00:00
-- url     : https://prove2.me/theorems/329584d6-6bb7-4fce-8295-6fffcd170117
-- title:
--   Scalar row inequalities of the actual-coverage constructor (overlap coefficient $q-q^2/4$; no new definitions)
-- statement:
--   This file introduces no new definitions. It proves denominator-free scalar inequalities behind the rows of the actual-coverage constructor, which selects a two-vertex mixture with weight $q/4$ on the second vertex. Throughout, $m=q-q^2/4$ is the overlap coefficient arising from the two-type mixture formula $\lambda+(1-s)a+sb-s(1-s)o$ at $s=q/4$.
--
--   The proved lemmas are:
--
--   - `overlap_coefficient_bounds`: for $0<q\le 2$, $0<q-q^2/4\le 1$.
--   - `actual_entry_segment`: if the entry edge $A-\delta z-r z(1-z)$ is at least $3/4$ at $z=x\le 1/2$ (with $\delta,r\ge 0$), it is at least $3/4$ at every $z\in[0,x]$, so every point of an initial partial edge is safe.
--   - `actual_prefix_margin`: eligibility and envelope slack together give the prefix inequality $\tfrac34(L+g)\le L+(1-q/4)u+(q/4)g_c-(q/4)(1-q/4)r_c$.
--   - `actual_suffix_min_crossing`: a bound for the suffix expression after minimizing over the partner residual (case $u\le y$ versus $y\le u$, using $\min(u,y)$), for $1\le q\le 2$.
--   - `actual_suffix_credit`: the credit threshold proves every suffix row after the last eligible one, with both sides of the crossing $q\delta\lessgtr B$ treated.
--   - `actual_low_suffix`: for a positive envelope $q\le 1$, eligibility alone gives all later suffix row inequalities.
--
--   These are the arithmetic core of the stage-by-stage safety proofs for the constructor in the $3/4$ certificate argument (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ConstructorScalar.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry

namespace ConsistentSubmodular

theorem overlap_coefficient_bounds (q : ℝ) (hq0 : 0 < q) (hq2 : q ≤ 2) :
    0 < q - q ^ 2 / 4 ∧ q - q ^ 2 / 4 ≤ 1 := by
  constructor
  · nlinarith [mul_pos hq0 (show 0 < 1 - q / 4 by linarith)]
  · nlinarith [sq_nonneg (q - 2)]

/-- Safety of every point of an initial partial edge, not only its endpoint. -/
theorem actual_entry_segment (A δ r x : ℝ)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hx : x ≤ 1 / 2)
    (hend : (3 : ℝ) / 4 ≤ A - δ * x - r * x * (1 - x))
    (z : ℝ) (_hz : 0 ≤ z) (hzx : z ≤ x) :
    (3 : ℝ) / 4 ≤ A - δ * z - r * z * (1 - z) := by
  have h1 : 0 ≤ x - z := sub_nonneg.mpr hzx
  have h2 : 0 ≤ δ + r * (1 - x - z) := by
    apply add_nonneg hδ
    apply mul_nonneg hr
    linarith
  nlinarith [mul_nonneg h1 h2]

theorem actual_prefix_margin (A q L g u gc rc : ℝ)
    (helig : 0 ≤ 4 * A - 3 - q * (A - gc) - (q - q ^ 2 / 4) * rc)
    (henv : 0 ≤ q * ((A - g) + (g - u)) + (L + g - A) +
      3 * (1 - A) - 4 * (g - u)) :
    (3 : ℝ) / 4 * (L + g) ≤
      L + (1 - q / 4) * u + (q / 4) * gc -
        (q / 4) * (1 - q / 4) * rc := by
  nlinarith

/-- Minimizing the suffix expression over the partner residual. -/
theorem actual_suffix_min_crossing (q u y : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    (3 - (q - q ^ 2 / 4)) * u ≤
      (4 - q) * u + (q - 1) * y - (q - q ^ 2 / 4) * min u y := by
  by_cases h : u ≤ y
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (show 0 ≤ q - 1 by linarith) (sub_nonneg.mpr h)]
  · have h' : y ≤ u := le_of_not_ge h
    rw [min_eq_right h']
    have hm : 0 ≤ (q - q ^ 2 / 4) - (q - 1) := by
      nlinarith [sq_nonneg q]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr h')]

/-- The credit threshold proves every suffix row after the last eligible one.
All comparisons are denominator-free, including both sides of the crossing. -/
theorem actual_suffix_credit (A B q m δ w v : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hm : m = q - q ^ 2 / 4)
    (hcredit : 2 * A * q - 3 * B ≤ q * v)
    (hnoelig : m * w ≤ (q - m) * δ + m * A - B)
    (hres : w ≤ A - δ) :
    0 ≤ (1 - m) * A + v + m * δ - (3 - m) * w := by
  have hq : 0 < q := by linarith
  obtain ⟨hm0, hm1⟩ := overlap_coefficient_bounds q hq hq2
  rw [← hm] at hm0 hm1
  have h3 : 0 ≤ 3 - m := by linarith
  have hcr : 0 ≤ q * v - 2 * A * q + 3 * B := by linarith
  by_cases hcross : q * δ ≤ B
  · have hid :
        q * m * ((1 - m) * A + v + m * δ - (3 - m) * w) =
          m * (q * v - 2 * A * q + 3 * B) +
          (q ^ 2 * (q - 1) / 4) * (B - q * δ) +
          q * (3 - m) * ((q - m) * δ + m * A - B - m * w) := by
      rw [hm]
      ring
    have h1 := mul_nonneg (le_of_lt hm0) hcr
    have h2 : 0 ≤ (q ^ 2 * (q - 1) / 4) * (B - q * δ) := by
      apply mul_nonneg
      · apply div_nonneg
        · exact mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hq1)
        · norm_num
      · exact sub_nonneg.mpr hcross
    have h3' := mul_nonneg (mul_nonneg (le_of_lt hq) h3)
      (sub_nonneg.mpr hnoelig)
    have hqm : 0 < q * m := mul_pos hq hm0
    nlinarith
  · have hid :
        q * ((1 - m) * A + v + m * δ - (3 - m) * w) =
          (q * v - 2 * A * q + 3 * B) + 3 * (q * δ - B) +
          q * (3 - m) * (A - δ - w) := by ring
    have h1 := mul_nonneg (mul_nonneg (le_of_lt hq) h3) (sub_nonneg.mpr hres)
    nlinarith

/-- For a positive envelope at most one, eligibility alone provides all
later actual row inequalities. -/
theorem actual_low_suffix (A B D q m δc wc vc δ w : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hm : m = q - q ^ 2 / 4)
    (hD : D = A - B)
    (henv : 0 ≤ q * (δc + wc) + vc + D - 4 * wc)
    (helig : 0 ≤ B - q * δc - m * (A - δc - wc))
    (hnoelig : B - q * δ - m * (A - δ - w) ≤ 0) :
    0 ≤ (1 - m) * A + vc + m * δ - (4 - q - m) * w := by
  have hid :
      q * ((1 - m) * A + vc + m * δ - (4 - q - m) * w) =
        q * (q * (δc + wc) + vc + D - 4 * wc) +
        4 * (B - q * δc - m * (A - δc - wc)) -
        (4 - q) * (B - q * δ - m * (A - δ - w)) := by
    rw [hm, hD]
    ring
  have h1 := mul_nonneg (le_of_lt hq) henv
  have h2 := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 4 - q by linarith) hnoelig
  nlinarith

end ConsistentSubmodular


