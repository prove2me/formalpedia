-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8Bridge
-- name    : CK_GeneralCK_PureGapE8Bridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:43:54.229191+00:00
-- url     : https://prove2.me/theorems/bf883d81-daba-40cf-a975-27f594fe3037
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8Bridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8Bridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8Bridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8Bridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8Bridge.lean)

import Definitions.Def_CK_GeneralCK_PureGapMeanStationarity
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.PureGapE8Bridge =====
section

/-!
# Exact bridge from pure-gap stationarity to equation (8)

This module introduces the manuscript's normalized `A,B,C,D` coordinates
in the lower-half chamber `a < c`, rewrites the two mean-stationarity
equations in terms of the normalized radial slope `e8Theta`, and proves the
algebraic equation-(79) identity.  For any left inverse `Q` of `e8Theta`, the
two facts combine to say that the equation-(8) determinant vanishes.
-/

namespace GeneralCK






/-- Right marginal contact coordinate. -/
noncomputable def e8A (a c e f : ℝ) : ℝ := (1 - 2 * c) / (2 * f)

/-- Left marginal contact coordinate. -/
noncomputable def e8B (a c e f : ℝ) : ℝ := (1 - 2 * a) / (2 * e)

/-- Center contact coordinate. -/
noncomputable def e8C (a c e f : ℝ) : ℝ := (1 - a - c) / (e + f)

/-- Mean-difference contact coordinate. -/
noncomputable def e8D (a c e f : ℝ) : ℝ := (c - a) / (e + f)






theorem deriv_F_radius_eq_e8Theta {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z = e8Theta (z / (2 * h)) := by
  rw [deriv_F_radius_normalize hz hh]
  unfold e8Theta
  congr 2
  field_simp [hh.ne']

theorem e8Theta_pos {x : ℝ} (hx : 0 < x) : 0 < e8Theta x := by
  unfold e8Theta
  have hz : 0 < 2 * x := by positivity
  rw [deriv_F_radius hz (by norm_num : (0 : ℝ) < 1)]
  have hv := radialContact_pos hz (by norm_num : (0 : ℝ) < 1)
  have hvh := radialContact_lt_half hz (by norm_num : (0 : ℝ) < 1)
  have hv1 : radialContact (2 * x) 1 < 1 := by linarith
  have hJ := J_pos hv hvh
  have hH := H_pos hv hv1
  have hcenter := radialContact_denominator_pos hz (by norm_num : (0 : ℝ) < 1)
  have hfrac : 0 <
      (2 * x) * H (radialContact (2 * x) 1) /
        (Real.log 2 * radialContact (2 * x) 1 *
          (1 - radialContact (2 * x) 1) *
          ((2 * x) * J (radialContact (2 * x) 1) + 2 * 1)) := by
    positivity
  linarith

theorem e8A_pos {a c e f : ℝ} (hc : c < 1 / 2) (hf : 0 < f) :
    0 < e8A a c e f := by
  unfold e8A
  apply div_pos
  · linarith
  · positivity

theorem e8D_pos {a c e f : ℝ} (hac : a < c) (he : 0 < e) (hf : 0 < f) :
    0 < e8D a c e f := by
  unfold e8D
  positivity

/-- The two raw stationarity equations become exactly equations (78) after
normalizing every radius by its entropy coordinate. -/
theorem stationarity_to_e8Theta {a c e f : ℝ}
    (hac : a < c) (hsum : a + c < 1) (ha : a < 1 / 2)
    (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hleft :
      -deriv (fun r => F r ((e + f) / 2)) (c - a) -
          deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
          deriv (fun r => F r e) (1 - 2 * a) = 0)
    (hright :
      deriv (fun r => F r ((e + f) / 2)) (c - a) -
          deriv (fun r => F r ((e + f) / 2)) (1 - a - c) +
          deriv (fun r => F r f) (1 - 2 * c) = 0) :
    e8Theta (e8C a c e f) =
        e8Theta (e8D a c e f) + e8Theta (e8A a c e f) ∧
      e8Theta (e8B a c e f) =
        e8Theta (e8D a c e f) + e8Theta (e8C a c e f) := by
  have hef : 0 < (e + f) / 2 := by linarith
  rw [deriv_F_radius_eq_e8Theta (sub_pos.mpr hac) hef,
    deriv_F_radius_eq_e8Theta (by linarith) hef,
    deriv_F_radius_eq_e8Theta (by linarith) he] at hleft
  rw [deriv_F_radius_eq_e8Theta (sub_pos.mpr hac) hef,
    deriv_F_radius_eq_e8Theta (by linarith) hef,
    deriv_F_radius_eq_e8Theta (by linarith) hf] at hright
  have hD : (c - a) / (2 * ((e + f) / 2)) = e8D a c e f := by
    unfold e8D
    field_simp [show e + f ≠ 0 by linarith]
  have hC : (1 - a - c) / (2 * ((e + f) / 2)) = e8C a c e f := by
    unfold e8C
    field_simp [show e + f ≠ 0 by linarith]
  have hB : (1 - 2 * a) / (2 * e) = e8B a c e f := rfl
  have hA : (1 - 2 * c) / (2 * f) = e8A a c e f := rfl
  rw [hD, hC, hB] at hleft
  rw [hD, hC, hA] at hright
  constructor <;> linarith

/-- The two linear coordinate balances immediately preceding equation (79). -/
theorem e8_coordinate_balances {a c e f : ℝ} (he : e ≠ 0) (hf : f ≠ 0)
    (hef : e + f ≠ 0) :
    e8B a c e f * e + e8A a c e f * f =
        e8C a c e f * (e + f) ∧
      -(e8A a c e f * f) + e8B a c e f * e =
        e8D a c e f * (e + f) := by
  unfold e8A e8B e8C e8D
  constructor <;> field_simp [he, hf, hef] <;> ring

/-- Exact cross-multiplied equation (79), with no denominator side
conditions needed in its statement. -/
theorem e8_cross_identity {a c e f : ℝ} (he : e ≠ 0) (hf : f ≠ 0)
    (hef : e + f ≠ 0) :
    (e8B a c e f - e8D a c e f) *
        (e8C a c e f - e8A a c e f) =
      (e8B a c e f - e8C a c e f) *
        (e8D a c e f + e8A a c e f) := by
  unfold e8A e8B e8C e8D
  field_simp [he, hf, hef]
  ring

/-- A left inverse for the normalized slope turns stationarity and the
coordinate identity into equality in the equation-(8) determinant. -/
theorem stationarity_e8Delta_eq_zero {a c e f : ℝ} {Q : ℝ → ℝ}
    (he : 0 < e) (hf : 0 < f)
    (hstat :
      e8Theta (e8C a c e f) =
          e8Theta (e8D a c e f) + e8Theta (e8A a c e f) ∧
        e8Theta (e8B a c e f) =
          e8Theta (e8D a c e f) + e8Theta (e8C a c e f))
    (hQ : Function.LeftInverse Q e8Theta) :
    e8Delta Q (e8Theta (e8D a c e f))
      (e8Theta (e8A a c e f)) = 0 := by
  have hA := hQ (e8A a c e f)
  have hB := hQ (e8B a c e f)
  have hC := hQ (e8C a c e f)
  have hD := hQ (e8D a c e f)
  have hst :
      e8Theta (e8D a c e f) + e8Theta (e8A a c e f) =
        e8Theta (e8C a c e f) := hstat.1.symm
  have h2st :
      2 * e8Theta (e8D a c e f) + e8Theta (e8A a c e f) =
        e8Theta (e8B a c e f) := by linarith [hstat.1, hstat.2]
  unfold e8Delta
  rw [hst, h2st, hA, hB, hC, hD]
  exact sub_eq_zero.mpr
    (e8_cross_identity (a := a) (c := c) he.ne' hf.ne' (by linarith))

/-- A smooth local minimum in the strict lower-half chamber would force
equality in equation (8). -/
theorem canonicalPureGap_localMin_e8Delta_eq_zero {a c e f : ℝ}
    {Q : ℝ → ℝ} (hac : a < c) (hsum : a + c < 1)
    (ha : a < 1 / 2) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hmin : IsLocalMin
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, c))
    (hQ : Function.LeftInverse Q e8Theta) :
    e8Delta Q (e8Theta (e8D a c e f))
      (e8Theta (e8A a c e f)) = 0 := by
  apply stationarity_e8Delta_eq_zero he hf _ hQ
  exact stationarity_to_e8Theta hac hsum ha hc he hf
    (canonicalPureGap_left_stationarity hac hsum ha he hf hmin)
    (canonicalPureGap_right_stationarity hac hsum hc he hf hmin)

/-- The exact logical handoff to the manuscript's strict equation-(8)
inequality: a global positive determinant excludes a smooth local minimum. -/
theorem not_localMin_of_e8_strict {a c e f : ℝ} {Q : ℝ → ℝ}
    (hac : a < c) (hsum : a + c < 1)
    (ha : a < 1 / 2) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hQ : Function.LeftInverse Q e8Theta)
    (hE8 : ∀ s t : ℝ, 0 < s → 0 < t → 0 < e8Delta Q s t) :
    ¬ IsLocalMin
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, c) := by
  intro hmin
  have hzero := canonicalPureGap_localMin_e8Delta_eq_zero hac hsum ha hc he hf hmin hQ
  have hs : 0 < e8Theta (e8D a c e f) :=
    e8Theta_pos (e8D_pos hac he hf)
  have ht : 0 < e8Theta (e8A a c e f) :=
    e8Theta_pos (e8A_pos hc hf)
  linarith [hE8 _ _ hs ht]

end GeneralCK

end


