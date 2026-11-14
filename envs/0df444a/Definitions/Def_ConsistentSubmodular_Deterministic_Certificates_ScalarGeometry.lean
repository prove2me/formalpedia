-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry
-- name    : ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:30.240197+00:00
-- url     : https://prove2.me/theorems/0067741a-5785-49f7-8c51-2b3a068b1e0f
-- title:
--   Scalar geometry for the finite checkpoint construction (no new definitions; edge discriminants and strong credit)
-- statement:
--   This file introduces no new definitions. It collects scalar inequalities about the quadratic profile $z\mapsto A-e\,z-r\,z(1-z)$ that describes the value of a certificate edge in the atomic-profile setting of Appendix B, with the safety level $3/4$ used throughout the clairvoyant certificates.
--
--   The proved lemmas are:
--
--   - `safe_edge_discriminant`: if $0\le e<r$ and the edge profile is at least $3/4$ for all $z\in[0,1]$, then evaluating at the interior minimizer $z=(e+r)/(2r)$ gives the denominator-free condition $(e+r)^2\le(4A-3)\,r$.
--   - `safe_relay_strong_credit`: a pessimistically safe forward relay preserves strong credit, i.e. for a child value $V$ either $V\ge 1/2$ or $1-g\le V(1-V)$, under the normalizations $g\le A\le 1$ and $0\le r\le g$.
--   - `strong_credit_baseline`: strong credit, together with $A\ge 3/4$, yields the baseline budget $2(1-A)\le L$ used by exits.
--   - `suff_terminal_vertex_edge`: a scalar criterion for the terminal edge of the minimum-overlap sufficient exit, showing $\tfrac34(L+G)\le L+(1-y)^2R+yG$ for all $y\in[0,1]$ from persistence $G\le L+w$ and the endpoint bound $\tfrac34(L+G)\le L+R-w/4$.
--
--   These are purely real-number facts with all case distinctions and divisions handled explicitly.
--
--   They support the construction of clairvoyant certificates for the deterministic bound $3/4$ (Section 3, Appendix B): the geometric safety of relays, access paths and terminal exits is reduced to the inequalities proved here.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ScalarGeometry.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarIdentities

namespace ConsistentSubmodular

/-- Evaluating a safe convex edge at its interior minimizer gives its
denominator-free discriminant condition. -/
theorem safe_edge_discriminant (A e r : ℝ) (he : 0 ≤ e) (her : e < r)
    (hsafe : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      (3 : ℝ) / 4 ≤ A - e * z - r * z * (1 - z)) :
    (e + r) ^ 2 ≤ (4 * A - 3) * r := by
  have hr : 0 < r := lt_of_le_of_lt he her
  have hden : 0 < 2 * r := by positivity
  have hz0 : 0 ≤ (e + r) / (2 * r) := by positivity
  have hz1 : (e + r) / (2 * r) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hs := hsafe ((e + r) / (2 * r)) hz0 hz1
  have hid :
      4 * r * (A - e * ((e + r) / (2 * r)) -
        r * ((e + r) / (2 * r)) * (1 - (e + r) / (2 * r)) - 3 / 4) =
      (4 * A - 3) * r - (e + r) ^ 2 := by
    field_simp
    ring
  have hm := mul_nonneg (by positivity : 0 ≤ 4 * r) (sub_nonneg.mpr hs)
  rw [hid] at hm
  linarith

/-- Every pessimistically safe forward relay preserves strong credit.
Only the canonical parent benchmark and persistence are needed. -/
theorem safe_relay_strong_credit (A g r V : ℝ)
    (hA : A ≤ 1) (hgA : g ≤ A) (hr : 0 ≤ r) (hrg : r ≤ g)
    (hV : g - r ≤ V)
    (hsafe : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      (3 : ℝ) / 4 ≤ A - (A - g) * z - r * z * (1 - z)) :
    (1 : ℝ) / 2 ≤ V ∨ 1 - g ≤ V * (1 - V) := by
  by_cases hlarge : (1 : ℝ) / 2 ≤ V
  · exact Or.inl hlarge
  right
  have hVhalf : V < 1 / 2 := lt_of_not_ge hlarge
  have hg : (3 : ℝ) / 4 ≤ g := by
    have := hsafe 1 (by norm_num) (by norm_num)
    norm_num at this
    linarith
  have hw0 : 0 ≤ g - r := sub_nonneg.mpr hrg
  have hw : g - r < 1 / 2 := lt_of_le_of_lt hV hVhalf
  have her : A - g < r := by linarith
  have hdisc := safe_edge_discriminant A (A - g) r (sub_nonneg.mpr hgA) her hsafe
  have hB : 0 < 4 * A - 3 := by
    have hsum : 0 < A - g + r := by linarith
    have hsq := sq_pos_of_pos hsum
    nlinarith
  have hidentity :
      (4 * A - 3) * ((g - r) * (1 - (g - r)) - (1 - g)) -
        ((4 * A - 3) * r - (A - g + r) ^ 2) =
      (1 - A) ^ 2 + 2 * (1 - A) * (1 - 2 * (g - r)) * (1 - (g - r)) := by
    ring
  have hproduct : 0 ≤ 2 * (1 - A) * (1 - 2 * (g - r)) * (1 - (g - r)) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hA)
      · linarith
    · linarith
  have hcredit : 1 - g ≤ (g - r) * (1 - (g - r)) := by
    nlinarith [sq_nonneg (1 - A)]
  have hmono : (g - r) * (1 - (g - r)) ≤ V * (1 - V) := by
    have := mul_nonneg (sub_nonneg.mpr hV)
      (by linarith : 0 ≤ 1 - V - (g - r))
    nlinarith
  exact hcredit.trans hmono

/-- The strong-credit condition provides the baseline budget used by exits. -/
theorem strong_credit_baseline (A L : ℝ) (_hA : A ≤ 1)
    (hcredit : (1 : ℝ) / 2 ≤ L + A - 1 ∨
      1 - A ≤ (L + A - 1) * (1 - (L + A - 1)))
    (hAlow : (3 : ℝ) / 4 ≤ A) : 2 * (1 - A) ≤ L := by
  rcases hcredit with h | h
  · linarith
  · nlinarith [sq_nonneg (L + A - 1)]

/-- Scalar terminal edge criterion for the minimum-overlap sufficient exit. The
parameter `w` is the smaller residual and `R` is the larger one. -/
theorem suff_terminal_vertex_edge (L G R w : ℝ)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (hR : 0 ≤ R) (hw : 0 ≤ w)
    (hpersist : G ≤ L + w)
    (hgood : (3 : ℝ) / 4 * (L + G) ≤ L + R - w / 4)
    (y : ℝ) (hy : 0 ≤ y) (_hy1 : y ≤ 1) :
    (3 : ℝ) / 4 * (L + G) ≤ L + (1 - y) ^ 2 * R + y * G := by
  have hend : (3 : ℝ) / 4 * (L + G) ≤ L + R := by linarith
  by_cases hz : R = 0
  · subst R
    nlinarith [mul_nonneg hy hG]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
  by_cases hsmall : L < G
  · have hRbound : G - L / 2 ≤ R := by linarith
    have hmul := mul_nonneg (sub_nonneg.mpr hRbound)
      (show 0 ≤ L + G by positivity)
    have hprod : G ^ 2 ≤ R * (L + G) := by
      nlinarith [mul_nonneg hL (show 0 ≤ G - L by linarith)]
    have hid := exit_square_identity L G R y
    nlinarith [sq_nonneg (2 * R * (1 - y) - G)]
  · have hGL : G ≤ L := le_of_not_gt hsmall
    by_cases hhalf : R ≤ G / 2
    · have h1 := mul_nonneg hy (show 0 ≤ G - 2 * R by linarith)
      have h2 := mul_nonneg hR (sq_nonneg y)
      nlinarith
    · have hprod : G ^ 2 ≤ R * (L + G) := by
        have h1 := mul_nonneg (show 0 ≤ R - G / 2 by linarith)
          (show 0 ≤ L + G by positivity)
        nlinarith [mul_nonneg hG (sub_nonneg.mpr hGL)]
      have hid := exit_square_identity L G R y
      nlinarith [sq_nonneg (2 * R * (1 - y) - G)]

end ConsistentSubmodular


