-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_TerminalActualScalar
-- name    : ConsistentSubmodular_Deterministic_Certificates_TerminalActualScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:39.053903+00:00
-- url     : https://prove2.me/theorems/e848be0b-f2c4-4092-9d2e-d9aa3349d127
-- title:
--   Terminal quadratic obstruction for actual exits: scalar contradictions and safety after the start (no new definitions)
-- statement:
--   This file introduces no new definitions. It studies the terminal exit expression $L+(1-y)^2u+yG$ against the level $\tfrac34(L+G)$, which is the value along the last exit edge in the actual-coverage constructor. Its minimum over $y$ is unsafe exactly in the obstructed configuration $u(L+G)<G^2$ with $G<2ub$.
--
--   The proved lemmas are:
--
--   - `normalized_exit_contradiction` and `normalized_exit_canonical_contradiction`: after the normalization $r=u/G\in(0,1)$ and $1<2br$, the hypotheses $G\le A$, $J<$ the quantity $G(r^2+1-r)/r$ and $4brA<3r+G(4br^2-4r+1)$ are inconsistent, under the budget $3\le A+2J$ or the canonical budget $1\le J$ (with $\tfrac12\le b\le 1$ respectively $\tfrac12\le b\le \tfrac34$). The elimination is division-free.
--   - `actual_terminal_no_bad_minimum`: under the envelope $4b(A-u)\le 3-3G+L$ and the anchor budget $3\le A+2(L+u)$, the obstructed configuration cannot occur.
--   - `actual_terminal_no_bad_minimum_canonical`: the same conclusion for $\tfrac12\le b\le\tfrac34$ using only the canonical budget $1\le L+u$.
--   - `terminal_quadratic_safe_after`: if the point $x$ is good and the obstructed configuration with $b=1-x$ is excluded, the entire subsequent edge $y\ge x$ is safe.
--
--   They guarantee that the terminal exit of the deterministic $3/4$ certificate (Appendix B) cannot dip below the safety level after the chosen starting mass.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/TerminalActualScalar.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry

namespace ConsistentSubmodular

theorem normalized_exit_contradiction (b r A G J : ℝ)
    (hb : (1 : ℝ) / 2 ≤ b) (hb1 : b ≤ 1)
    (hr : 0 < r) (hr1 : r < 1) (hbr : 1 < 2 * b * r)
    (hGA : G ≤ A) (hbudget : 3 ≤ A + 2 * J)
    (hJ : r * J < G * (r ^ 2 + 1 - r))
    (hA : 4 * b * r * A < 3 * r + G * (4 * b * r ^ 2 - 4 * r + 1)) : False := by
  let c := r ^ 2 + 1 - r
  let X := 4 * b * r
  let E := 4 * b * r ^ 2 - 4 * r + 1
  let D := X - E
  let F := E + 8 * b * c
  have hbpos : 0 < b := by linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hrhalf : (1 : ℝ) / 2 < r := by
    have := mul_nonneg (sub_nonneg.mpr hb1) (le_of_lt hr)
    nlinarith
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [sq_nonneg (r - 1 / 2)]
  have hDbound : r + 2 * c < D := by
    have h1 : 0 < (4 * b + 2) * r - 3 := by nlinarith
    have h2 := mul_pos (sub_pos.mpr hr1) h1
    dsimp [D, X, E, c]
    nlinarith only [h2]
  have hD : 0 < D := by linarith
  have hF : 0 < F := by
    have hcoef : 0 ≤ 12 * r ^ 2 - 8 * r + 8 := by
      nlinarith [sq_nonneg (3 * r - 1)]
    have hm := mul_nonneg (sub_nonneg.mpr hb) hcoef
    dsimp [F, E, c]
    nlinarith [sq_nonneg (3 * r - 2)]
  have hGD : G * D < 3 * r := by
    have hxga := mul_le_mul_of_nonneg_left hGA (le_of_lt hX)
    change X * A < 3 * r + G * E at hA
    dsimp [D]
    nlinarith only [hxga, hA]
  have htotal : X * (A + 2 * J) < 3 * r + G * F := by
    have hJ' := mul_lt_mul_of_pos_left hJ (show 0 < 8 * b by positivity)
    change X * A < 3 * r + G * E at hA
    dsimp [X, F, c, E] at *
    nlinarith only [hJ', hA]
  have hbad : X * D * (A + 2 * J) < 3 * X * (r + 2 * c) := by
    calc
      X * D * (A + 2 * J) = D * (X * (A + 2 * J)) := by ring
      _ < D * (3 * r + G * F) := mul_lt_mul_of_pos_left htotal hD
      _ = 3 * r * D + F * (G * D) := by ring
      _ < 3 * r * D + F * (3 * r) :=
        by linarith [mul_lt_mul_of_pos_left hGD hF]
      _ = 3 * X * (r + 2 * c) := by dsimp [X, D, E, F, c]; ring
  have hlow : 3 * X * D ≤ X * D * (A + 2 * J) := by
    nlinarith only [mul_le_mul_of_nonneg_left hbudget (le_of_lt (mul_pos hX hD))]
  have hhigh : 3 * X * (r + 2 * c) < 3 * X * D :=
    mul_lt_mul_of_pos_left hDbound (by positivity)
  linarith

/-- Under the envelope and anchor budget, the terminal quadratic cannot
have an unsafe minimum strictly after the chosen starting mass. -/
theorem actual_terminal_no_bad_minimum (A G L u b : ℝ)
    (hL : 0 ≤ L) (hu : 0 ≤ u) (huG : u ≤ G) (hGA : G ≤ A)
    (hb : (1 : ℝ) / 2 ≤ b) (hb1 : b ≤ 1)
    (hbudget : 3 ≤ A + 2 * (L + u))
    (henv : 4 * b * (A - u) ≤ 3 - 3 * G + L) :
    ¬ (u * (L + G) < G ^ 2 ∧ G < 2 * u * b) := by
  rintro ⟨hmin, hbranch⟩
  have hG0 : 0 ≤ G := hu.trans huG
  have hG : 0 < G := by
    have := mul_nonneg hu (show 0 ≤ L + G by positivity)
    nlinarith
  have hu0 : 0 < u := by
    by_contra hn
    have : u = 0 := le_antisymm (le_of_not_gt hn) hu
    subst u
    nlinarith
  have huG' : u < G := by
    have := mul_nonneg hu hL
    nlinarith
  let r := u / G
  have hr : 0 < r := div_pos hu0 hG
  have hr1 : r < 1 := (div_lt_one hG).mpr huG'
  have hrG : r * G = u := div_mul_cancel₀ u (ne_of_gt hG)
  have hbr : 1 < 2 * b * r := by
    apply (mul_lt_mul_iff_right₀ hG).mp
    calc
      G * 1 = G := by ring
      _ < 2 * u * b := hbranch
      _ = G * (2 * b * r) := by rw [← hrG]; ring
  have hmin' : r * (L + G) < G := by
    apply (mul_lt_mul_iff_left₀ hG).mp
    calc
      r * (L + G) * G = u * (L + G) := by rw [← hrG]; ring
      _ < G ^ 2 := hmin
      _ = G * G := by ring
  have hJ : r * (L + u) < G * (r ^ 2 + 1 - r) := by
    calc
      r * (L + u) = r * (L + G) + r * (u - G) := by ring
      _ < G + r * (u - G) := by linarith
      _ = G * (r ^ 2 + 1 - r) := by rw [← hrG]; ring
  have hA : 4 * b * r * A < 3 * r + G * (4 * b * r ^ 2 - 4 * r + 1) := by
    have henv' := mul_le_mul_of_nonneg_left henv (le_of_lt hr)
    rw [← hrG] at henv' hJ
    nlinarith only [henv', hJ]
  exact normalized_exit_contradiction b r A G (L + u)
    hb hb1 hr hr1 hbr hGA hbudget hJ hA

theorem normalized_exit_canonical_contradiction (b r A G J : ℝ)
    (hb : (1 : ℝ) / 2 ≤ b) (hb3 : b ≤ 3 / 4)
    (hr : 0 < r) (hr1 : r < 1) (hbr : 1 < 2 * b * r)
    (hGA : G ≤ A) (hbudget : 1 ≤ J)
    (hJ : r * J < G * (r ^ 2 + 1 - r))
    (hA : 4 * b * r * A < 3 * r + G * (4 * b * r ^ 2 - 4 * r + 1)) : False := by
  let c := r ^ 2 + 1 - r
  let X := 4 * b * r
  let E := 4 * b * r ^ 2 - 4 * r + 1
  let D := X - E
  have hbpos : 0 < b := by linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hrthird : (2 : ℝ) / 3 < r := by
    have := mul_nonneg (sub_nonneg.mpr hb3) (le_of_lt hr)
    nlinarith
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [sq_nonneg (r - 1 / 2)]
  have hDbound : 3 * c < D := by
    have h1 : 0 < (4 * b + 3) * r - 4 := by nlinarith
    have h2 := mul_pos (sub_pos.mpr hr1) h1
    dsimp [D, X, E, c]
    nlinarith only [h2]
  have hD : 0 < D := by linarith
  have hGD : G * D < 3 * r := by
    have hxga := mul_le_mul_of_nonneg_left hGA (le_of_lt hX)
    change X * A < 3 * r + G * E at hA
    dsimp [D]
    nlinarith only [hxga, hA]
  have hrGc : r < G * c := by
    have := mul_le_mul_of_nonneg_left hbudget (le_of_lt hr)
    change r * J < G * c at hJ
    linarith
  have h1 := mul_lt_mul_of_pos_right hrGc hD
  have h2 := mul_lt_mul_of_pos_right hGD hc
  have h3 := mul_lt_mul_of_pos_left hDbound hr
  nlinarith only [h1, h2, h3]

/-- For mass parameters between one and two, canonical persistence suffices;
the stronger low-mass baseline budget is unnecessary. -/
theorem actual_terminal_no_bad_minimum_canonical (A G L u b : ℝ)
    (hL : 0 ≤ L) (hu : 0 ≤ u) (huG : u ≤ G) (hGA : G ≤ A)
    (hb : (1 : ℝ) / 2 ≤ b) (hb3 : b ≤ 3 / 4)
    (hbudget : 1 ≤ L + u)
    (henv : 4 * b * (A - u) ≤ 3 - 3 * G + L) :
    ¬ (u * (L + G) < G ^ 2 ∧ G < 2 * u * b) := by
  rintro ⟨hmin, hbranch⟩
  have hG0 : 0 ≤ G := hu.trans huG
  have hG : 0 < G := by
    have := mul_nonneg hu (show 0 ≤ L + G by positivity)
    nlinarith
  have hu0 : 0 < u := by
    by_contra hn
    have : u = 0 := le_antisymm (le_of_not_gt hn) hu
    subst u
    nlinarith
  have huG' : u < G := by
    have := mul_nonneg hu hL
    nlinarith
  let r := u / G
  have hr : 0 < r := div_pos hu0 hG
  have hr1 : r < 1 := (div_lt_one hG).mpr huG'
  have hrG : r * G = u := div_mul_cancel₀ u (ne_of_gt hG)
  have hbr : 1 < 2 * b * r := by
    apply (mul_lt_mul_iff_right₀ hG).mp
    calc
      G * 1 = G := by ring
      _ < 2 * u * b := hbranch
      _ = G * (2 * b * r) := by rw [← hrG]; ring
  have hmin' : r * (L + G) < G := by
    apply (mul_lt_mul_iff_left₀ hG).mp
    calc
      r * (L + G) * G = u * (L + G) := by rw [← hrG]; ring
      _ < G ^ 2 := hmin
      _ = G * G := by ring
  have hJ : r * (L + u) < G * (r ^ 2 + 1 - r) := by
    calc
      r * (L + u) = r * (L + G) + r * (u - G) := by ring
      _ < G + r * (u - G) := by linarith
      _ = G * (r ^ 2 + 1 - r) := by rw [← hrG]; ring
  have hA : 4 * b * r * A < 3 * r + G * (4 * b * r ^ 2 - 4 * r + 1) := by
    have henv' := mul_le_mul_of_nonneg_left henv (le_of_lt hr)
    rw [← hrG] at henv' hJ
    nlinarith only [henv', hJ]
  exact normalized_exit_canonical_contradiction b r A G (L + u)
    hb hb3 hr hr1 hbr hGA hbudget hJ hA

/-- Starting from a good point, excluding the obstructed minimum certifies
the entire subsequent terminal edge. -/
theorem terminal_quadratic_safe_after (L G u x : ℝ)
    (hu : 0 ≤ u) (hG : 0 ≤ G)
    (hgood : (3 : ℝ) / 4 * (L + G) ≤ L + (1 - x) ^ 2 * u + x * G)
    (hno : ¬ (u * (L + G) < G ^ 2 ∧ G < 2 * u * (1 - x)))
    (y : ℝ) (hxy : x ≤ y) :
    (3 : ℝ) / 4 * (L + G) ≤ L + (1 - y) ^ 2 * u + y * G := by
  by_cases hu0 : u = 0
  · subst u
    have := mul_le_mul_of_nonneg_right hxy hG
    nlinarith
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  by_cases hmin : u * (L + G) < G ^ 2
  · have hderiv : 2 * u * (1 - x) ≤ G := by
      by_contra hn
      exact hno ⟨hmin, lt_of_not_ge hn⟩
    have hfactor : 0 ≤ G - u * (2 - x - y) := by
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hxy)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hfactor]
  · have hid := exit_square_identity L G u y
    have hdisc : G ^ 2 ≤ u * (L + G) := le_of_not_gt hmin
    nlinarith [sq_nonneg (2 * u * (1 - y) - G)]

end ConsistentSubmodular


