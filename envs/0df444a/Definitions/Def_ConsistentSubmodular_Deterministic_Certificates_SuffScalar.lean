-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffScalar
-- name    : ConsistentSubmodular_Deterministic_Certificates_SuffScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:14.304306+00:00
-- url     : https://prove2.me/theorems/d2fb5dc3-1885-4963-9ca6-0c94f3b7341a
-- title:
--   Denominator-free scalar inequalities for the sufficient constructor and the minimum-overlap bound
-- statement:
--   This file contains no definitions; it proves real-number inequalities that are used by the sufficient constructor on atomic profiles. The sufficient row at a stage is the lower bound $\mathrm{row}=L+(1-q/4)u+(q/4)z-\min(u,z)/4$ obtained for the value of the mixture $(1-x)\delta_h+x\delta_c$, $x=q/4$, when the overlap of the two candidates is only known to be at most $\min(u,z)$; here $L$ is a baseline, $g$ a designated value, $u,z$ are residuals of the two candidates, $A$ is the anchor's designated value, and the goal is $\tfrac34(L+g)\le\mathrm{row}$.
--
--   - `suff_prefix_margin`: the prefix margin. If the sufficient eligibility $0\le(g_c-\rho_{ac})-(q-1)(A-g_c)-3(1-A)$ and the envelope inequality $0\le q(A-u)+(L+g-A)+3(1-A)-4(g-u)$ hold, then $\tfrac34(L+g)\le L+(1-q/4)u+(q/4)g_c-\rho_{ac}/4$.
--   - `suff_min_crossing_low` and `suff_min_crossing_high`: the crossing inequalities for the minimum term, $2u\le(4-q)u+(q-1)z-\min(u,z)$ for $1\le q\le2$, and $(4-q)u\le(4-q)u+(q-1)z-\min(u,z)$ for $q\ge2$, $z\ge0$.
--   - `suff_suffix_margin_credit`: the suffix margin for $\tfrac32\le q\le3$ under persistence $P_c\le L+z$, failure of the eligibility test at $t$, and the credit inequality $2Aq-3(4A-3)\le q(P_c-A)$; both the cases $q\le2$ and $q\ge2$ share the same denominator-free credit.
--   - `suff_suffix_margin_root_low`: the corresponding margin for the root-type case $1\le q\le\tfrac32$, $g\le1$, $P_c\ge1$.
--   - `suff_inactive_margin`: for $x\in[0,1]$ and $3g\le L$ (an inactive stage), $\tfrac34(L+g)\le L+(1-x)u+xz-\min(u,z)/4$.
--
--   Together these supply the stage-by-stage guarantees of the sufficient constructor, which produces the checkpoint certificates of the deterministic lower bound of Theorem 7 in Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SuffScalar.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarIdentities

namespace ConsistentSubmodular

theorem suff_prefix_margin (A q L g u gc ac : ℝ)
    (helig : 0 ≤ (gc - ac) - (q - 1) * (A - gc) - 3 * (1 - A))
    (henv : 0 ≤ q * (A - u) + (L + g - A) + 3 * (1 - A) - 4 * (g - u)) :
    (3 : ℝ) / 4 * (L + g) ≤ L + (1 - q / 4) * u + q / 4 * gc - ac / 4 := by
  nlinarith only [helig, henv]

theorem suff_min_crossing_low (u z q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    2 * u ≤ (4 - q) * u + (q - 1) * z - min u z := by
  by_cases huz : u ≤ z
  · rw [min_eq_left huz]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr huz)]
  · have hzu : z ≤ u := le_of_not_ge huz
    rw [min_eq_right hzu]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (sub_nonneg.mpr hzu)]

theorem suff_min_crossing_high (u z q : ℝ) (hz : 0 ≤ z) (hq2 : 2 ≤ q) :
    (4 - q) * u ≤ (4 - q) * u + (q - 1) * z - min u z := by
  have := mul_nonneg (show 0 ≤ q - 2 by linarith) hz
  have := min_le_right u z
  nlinarith

/-- The two tail optimizations share the same denominator-free credit. -/
theorem suff_suffix_margin_credit (A q L g u z Pc : ℝ)
    (hq : (3 : ℝ) / 2 ≤ q) (hq3 : q ≤ 3) (hu : 0 ≤ u) (hz : 0 ≤ z)
    (hpersist : Pc ≤ L + z)
    (hnoelig : (g - u) - (q - 1) * (A - g) - 3 * (1 - A) ≤ 0)
    (hcredit : 2 * A * q - 3 * (4 * A - 3) ≤ q * (Pc - A)) :
    (3 : ℝ) / 4 * (L + g) ≤
      L + (1 - q / 4) * u + q / 4 * z - min u z / 4 := by
  have hqpos : 0 < q := by linarith
  by_cases hq2 : q ≤ 2
  · have hcross := suff_min_crossing_low u z q (by linarith) hq2
    have hbound := mul_nonneg (show 0 ≤ 2 * q - 3 by linarith) hu
    have hmargin : 0 ≤ q * ((Pc - A) + (A - g) - 2 * (g - u)) := by
      nlinarith only [hcredit, hnoelig, hbound]
    have htail : 0 ≤ (Pc - A) + (A - g) - 2 * (g - u) := by
      exact nonneg_of_mul_nonneg_right hmargin hqpos
    nlinarith only [htail, hpersist, hcross]
  · have hq2' : 2 ≤ q := le_of_not_ge hq2
    have hcross := suff_min_crossing_high u z q hz hq2'
    have hcoef : 0 ≤ (3 - q) * (q - 1) :=
      mul_nonneg (sub_nonneg.mpr hq3) (by linarith)
    have hbound := mul_nonneg hcoef hu
    have hmargin : 0 ≤ q * ((2 - q) * A + (Pc - A) +
        (q - 1) * (A - g) - (4 - q) * (g - u)) := by
      nlinarith only [hcredit, hnoelig, hbound]
    have htail : 0 ≤ (2 - q) * A + (Pc - A) +
        (q - 1) * (A - g) - (4 - q) * (g - u) :=
      nonneg_of_mul_nonneg_right hmargin hqpos
    nlinarith only [htail, hpersist, hcross]

theorem suff_suffix_margin_root_low (q L g u z Pc : ℝ)
    (hq1 : 1 ≤ q) (hq : q ≤ (3 : ℝ) / 2) (hg : g ≤ 1)
    (hPc : 1 ≤ Pc) (hpersist : Pc ≤ L + z)
    (hnoelig : (g - u) - (q - 1) * (1 - g) ≤ 0) :
    (3 : ℝ) / 4 * (L + g) ≤
      L + (1 - q / 4) * u + q / 4 * z - min u z / 4 := by
  have hcross := suff_min_crossing_low u z q hq1 (by linarith)
  have hbound := mul_nonneg (show 0 ≤ 3 - 2 * q by linarith) (sub_nonneg.mpr hg)
  nlinarith only [hPc, hpersist, hnoelig, hcross, hbound]

theorem suff_inactive_margin (L g u z x : ℝ)
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hL : 3 * g ≤ L) :
    (3 : ℝ) / 4 * (L + g) ≤ L + (1 - x) * u + x * z - min u z / 4 := by
  have hw : 0 ≤ min u z := le_min hu hz
  have h1 := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (min_le_left u z))
  have h2 := mul_nonneg hx (sub_nonneg.mpr (min_le_right u z))
  nlinarith only [hw, h1, h2, hL]

end ConsistentSubmodular


