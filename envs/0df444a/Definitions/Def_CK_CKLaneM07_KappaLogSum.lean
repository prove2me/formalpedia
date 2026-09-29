-- Prove2me | Definitions.Def_CK_CKLaneM07_KappaLogSum
-- name    : CK_CKLaneM07_KappaLogSum
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:21:43.612298+00:00
-- url     : https://prove2.me/theorems/13799f45-98d1-4ab4-a84e-84fcffa140bf
-- title:
--   Courtade–Kumar proof module `CKLaneM07.KappaLogSum` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.KappaLogSum` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.KappaLogSum` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.KappaLogSum (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/KappaLogSum.lean)

import Definitions.Def_CK_GeneralCK_PsiLogSumOwner
import Definitions.Def_CK_GeneralCK_LogSum

-- ===== source module CKLaneM07.KappaLogSum =====
section

/-!
# Lane M07: the kappa-enhanced global log-sum cost floor

The archive (`same_side/COVER.py`) uses the log-sum coefficient
`beta = min(kap(a), kap(b)) / (2 b (1-a))` with
`kap(z) = min(z / (-(1-z) log(1-z)), (1-z) / (-z log z))`.
The corpus floor `GeneralCK.LogSum.cost_lower_bound` is the case `kap = 1`.

The improvement rests on the pointwise divergence bound (natural logs)
`κ · D(u‖a) ≤ χ²(u‖a) = (u-a)²/(a(1-a))` for every `u ∈ (0,1)`, valid whenever `0 ≤ κ ≤ 2`,
`κ · D(0‖a) ≤ χ²(0‖a)` and `κ · D(1‖a) ≤ χ²(1‖a)` (`kappa_klN`).  Proof: `g = χ² - κ D` has
`g(a) = g'(a) = 0`, `g'' = 2/(a(1-a)) - κ/(u(1-u))`, which is `≥ 0` exactly on `[u₁,u₂]`
(`u(1-u) ≥ κ a(1-a)/2`, an interval containing `a` because `κ ≤ 2`) and `≤ 0` outside; so `g`
is convex on `[u₁,u₂]` (tangent at `a`) and concave on `[0,u₁]`, `[u₂,1]` (endpoint values).
Averaging over a finite law as in `LogSum.cost_lower_bound` gives `kappa_cost_lower_bound`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM07

open GeneralCK Set

/-- KL divergence `D(u‖a)` in nats, written so that it is continuous in `u` on `ℝ`. -/
noncomputable def klN (a u : ℝ) : ℝ :=
  u * Real.log u - u * Real.log a + ((1 - u) * Real.log (1 - u) - (1 - u) * Real.log (1 - a))

/-- `χ²(u‖a) - κ D(u‖a)`. -/
noncomputable def kg (a κ u : ℝ) : ℝ := (u - a) ^ 2 / (a * (1 - a)) - κ * klN a u

/-- Its derivative on `(0,1)`. -/
noncomputable def kg1 (a κ u : ℝ) : ℝ :=
  2 * (u - a) / (a * (1 - a)) - κ * (Real.log u - Real.log a - Real.log (1 - u) + Real.log (1 - a))

/-- Its second derivative on `(0,1)`. -/
noncomputable def kg2 (a κ u : ℝ) : ℝ := 2 / (a * (1 - a)) - κ * (1 / u + 1 / (1 - u))

theorem klN_continuous (a : ℝ) : Continuous (klN a) := by
  have h1 : Continuous fun u : ℝ => u * Real.log u := Real.continuous_mul_log
  have h2 : Continuous fun u : ℝ => (1 - u) * Real.log (1 - u) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact (h1.sub (continuous_id.mul continuous_const)).add
    (h2.sub ((continuous_const.sub continuous_id).mul continuous_const))

theorem kg_continuous (a κ : ℝ) : Continuous (kg a κ) :=
  (((continuous_id.sub continuous_const).pow 2).div_const _).sub
    (continuous_const.mul (klN_continuous a))

theorem hasDerivAt_klN {a u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (klN a) (Real.log u - Real.log a - Real.log (1 - u) + Real.log (1 - a)) u := by
  have hu1' : (1 - u) ≠ 0 := (sub_pos.mpr hu1).ne'
  have h1 : HasDerivAt (fun u : ℝ => u * Real.log u) (Real.log u + 1) u :=
    Real.hasDerivAt_mul_log hu0.ne'
  have h2 := ((hasDerivAt_id' u).const_sub 1).mul (((hasDerivAt_id' u).const_sub 1).log hu1')
  have h3 := (hasDerivAt_id' u).mul_const (Real.log a)
  have h4 := ((hasDerivAt_id' u).const_sub 1).mul_const (Real.log (1 - a))
  have hd := (h1.sub h3).add (h2.sub h4)
  show HasDerivAt (fun u : ℝ =>
    u * Real.log u - u * Real.log a + ((1 - u) * Real.log (1 - u) - (1 - u) * Real.log (1 - a))) _ u
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_kg {a κ u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (kg a κ) (kg1 a κ u) u := by
  have hsq := (((hasDerivAt_id' u).sub_const a).pow 2).div_const (a * (1 - a))
  have hd := hsq.sub ((hasDerivAt_klN (a := a) hu0 hu1).const_mul κ)
  show HasDerivAt (fun u : ℝ => (u - a) ^ 2 / (a * (1 - a)) - κ * klN a u) _ u
  refine hd.congr_deriv ?_
  unfold kg1
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

theorem hasDerivAt_kg1 {a κ u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (kg1 a κ) (kg2 a κ u) u := by
  have hu1' : (1 - u) ≠ 0 := (sub_pos.mpr hu1).ne'
  have h1 := (((hasDerivAt_id' u).sub_const a).const_mul 2).div_const (a * (1 - a))
  have hl1 := Real.hasDerivAt_log hu0.ne'
  have hl2 := ((hasDerivAt_id' u).const_sub 1).log hu1'
  have hin := ((hl1.sub_const (Real.log a)).sub hl2).add_const (Real.log (1 - a))
  have hd := h1.sub (hin.const_mul κ)
  show HasDerivAt (fun u : ℝ => 2 * (u - a) / (a * (1 - a)) -
    κ * (Real.log u - Real.log a - Real.log (1 - u) + Real.log (1 - a))) _ u
  refine hd.congr_deriv ?_
  unfold kg2
  field_simp
  ring

theorem kg2_eq {a κ u : ℝ} (ha : 0 < a) (ha1 : a < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    kg2 a κ u = (2 * (u * (1 - u)) - κ * (a * (1 - a))) / ((a * (1 - a)) * (u * (1 - u))) := by
  have ha' : a ≠ 0 := ha.ne'
  have h1a : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  have hU : u ≠ 0 := hu0.ne'
  have hU1 : 1 - u ≠ 0 := (sub_pos.mpr hu1).ne'
  unfold kg2
  field_simp
  ring

theorem kg_self (a κ : ℝ) : kg a κ a = 0 := by
  unfold kg klN; ring

theorem kg1_self (a κ : ℝ) : kg1 a κ a = 0 := by
  unfold kg1; ring

theorem kg_zero {a κ : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    kg a κ 0 = a / (1 - a) - κ * (-Real.log (1 - a)) := by
  have hA : a * (1 - a) ≠ 0 := (mul_pos ha (sub_pos.mpr ha1)).ne'
  have h1a : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  unfold kg klN
  simp only [zero_mul, sub_zero, Real.log_one, mul_zero, one_mul, zero_sub]
  field_simp
  ring

theorem kg_one {a κ : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    kg a κ 1 = (1 - a) / a - κ * (-Real.log a) := by
  have h1a : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  have ha' : a ≠ 0 := ha.ne'
  unfold kg klN
  simp only [sub_self, zero_mul, Real.log_one, mul_zero, one_mul, zero_sub]
  field_simp
  ring

/-- The divergence bound `κ D(u‖a) ≤ χ²(u‖a)`. -/
theorem kappa_klN {a κ u : ℝ} (ha : 0 < a) (ha1 : a < 1) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (h0 : κ * (-Real.log (1 - a)) ≤ a / (1 - a)) (h1 : κ * (-Real.log a) ≤ (1 - a) / a)
    (hu0 : 0 < u) (hu1 : u < 1) :
    κ * klN a u ≤ (u - a) ^ 2 / (a * (1 - a)) := by
  suffices hg : 0 ≤ kg a κ u by unfold kg at hg; linarith
  -- the two roots of `u (1-u) = c`, `c = κ a (1-a) / 2`
  set c : ℝ := κ * (a * (1 - a)) / 2 with hcdef
  have hA : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha1)
  have hc0 : 0 ≤ c := by positivity
  have hcA : c ≤ a * (1 - a) := by rw [hcdef]; nlinarith
  have hA4 : a * (1 - a) ≤ 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hdisc : 0 ≤ 1 - 4 * c := by linarith
  set sq : ℝ := Real.sqrt (1 - 4 * c) with hsqdef
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hsq2 : sq ^ 2 = 1 - 4 * c := Real.sq_sqrt hdisc
  have hsq1 : sq ≤ 1 := by nlinarith
  set u1 : ℝ := (1 - sq) / 2 with hu1def
  set u2 : ℝ := (1 + sq) / 2 with hu2def
  have hfac : ∀ x : ℝ, x * (1 - x) - c = (x - u1) * (u2 - x) := by
    intro x; rw [hu1def, hu2def]; nlinarith [hsq2]
  have hu1_0 : 0 ≤ u1 := by rw [hu1def]; linarith
  have hu2_1 : u2 ≤ 1 := by rw [hu2def]; linarith
  have hu12 : u1 ≤ u2 := by rw [hu1def, hu2def]; linarith
  have hu1_half : u1 ≤ 1 / 2 := by rw [hu1def]; linarith
  have hu2_half : 1 / 2 ≤ u2 := by rw [hu2def]; linarith
  -- `a ∈ [u1, u2]`
  have haS : a ∈ Icc u1 u2 := by
    have hp : 0 ≤ (a - u1) * (u2 - a) := by rw [← hfac]; linarith
    constructor
    · by_contra hlt
      have hlt' : a < u1 := not_le.mp hlt
      have : (a - u1) * (u2 - a) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith
    · by_contra hlt
      have hlt' : u2 < a := not_le.mp hlt
      have : (a - u1) * (u2 - a) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
      linarith
  -- sign of the second derivative
  have hsign : ∀ x : ℝ, 0 < x → x < 1 → (0 ≤ kg2 a κ x ↔ c ≤ x * (1 - x)) := by
    intro x hx0 hx1
    have hX : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
    rw [kg2_eq ha ha1 hx0 hx1]
    constructor
    · intro h
      have hden : 0 < (a * (1 - a)) * (x * (1 - x)) := mul_pos hA hX
      have := (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hden))
      rw [hcdef]; linarith
    · intro h
      apply div_nonneg _ (mul_pos hA hX).le
      rw [hcdef] at h; linarith
  have hderiv1 : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (kg a κ) (kg1 a κ x) x :=
    fun x hx => hasDerivAt_kg hx.1 hx.2
  have hderiv2 : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (kg1 a κ) (kg2 a κ x) x :=
    fun x hx => hasDerivAt_kg1 hx.1 hx.2
  -- (R1) convexity on [u1, u2] and the tangent at `a`
  have hconv : ConvexOn ℝ (Icc u1 u2) (kg a κ) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc u1 u2) (f' := kg1 a κ) (f'' := kg2 a κ)
    · exact (kg_continuous a κ).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x < 1 := by linarith [hx.2]
      rw [hsign x hx0 hx1, ← sub_nonneg, hfac]
      exact mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have hda : HasDerivAt (kg a κ) 0 a := by
    have := hderiv1 a ⟨ha, ha1⟩
    rwa [kg1_self] at this
  have hR1 : ∀ x ∈ Icc u1 u2, 0 ≤ kg a κ x := by
    intro x hx
    rcases lt_trichotomy x a with hxa | hxa | hxa
    · have hs := hconv.slope_le_of_hasDerivAt hx haS hxa hda
      rw [slope_def_field, kg_self, div_le_iff₀ (by linarith)] at hs
      linarith
    · rw [hxa, kg_self]
    · have hs := hconv.le_slope_of_hasDerivAt haS hx hxa hda
      rw [slope_def_field, kg_self, le_div_iff₀ (by linarith)] at hs
      linarith
  -- (R2) concavity on [u2, 1]
  have hconc2 : ConcaveOn ℝ (Icc u2 1) (kg a κ) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc u2 1) (f' := kg1 a κ) (f'' := kg2 a κ)
    · exact (kg_continuous a κ).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv1 x ⟨by linarith [hx.1], hx.2⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv2 x ⟨by linarith [hx.1], hx.2⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x < 1 := hx.2
      rw [kg2_eq ha ha1 hx0 hx1]
      have hX : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
      apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos hA hX).le
      have hneg : x * (1 - x) - c ≤ 0 := by
        rw [hfac]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) (by linarith [hx.1])
      rw [hcdef] at hneg; linarith
  have hk1 : 0 ≤ kg a κ 1 := by rw [kg_one ha ha1]; linarith
  have hk0 : 0 ≤ kg a κ 0 := by rw [kg_zero ha ha1]; linarith
  -- (R3) concavity on [0, u1]
  have hconc0 : ConcaveOn ℝ (Icc 0 u1) (kg a κ) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 u1) (f' := kg1 a κ) (f'' := kg2 a κ)
    · exact (kg_continuous a κ).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv1 x ⟨hx.1, by linarith [hx.2]⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv2 x ⟨hx.1, by linarith [hx.2]⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : x < 1 := by linarith [hx.2]
      rw [kg2_eq ha ha1 hx0 hx1]
      have hX : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
      apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos hA hX).le
      have hneg : x * (1 - x) - c ≤ 0 := by
        rw [hfac]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (by linarith [hx.2])
      rw [hcdef] at hneg; linarith
  -- (R4) cover `(0,1)` by the three intervals
  rcases le_or_gt u u1 with hle1 | hgt1
  · have hm := hconc0.min_le_of_mem_Icc (show (0 : ℝ) ∈ Icc 0 u1 from ⟨le_rfl, hu1_0⟩)
      (show u1 ∈ Icc 0 u1 from ⟨hu1_0, le_rfl⟩) (show u ∈ Icc 0 u1 from ⟨hu0.le, hle1⟩)
    have hb := hR1 u1 ⟨le_rfl, hu12⟩
    exact (le_min hk0 hb).trans hm
  · rcases le_or_gt u u2 with hle2 | hgt2
    · exact hR1 u ⟨hgt1.le, hle2⟩
    · have hm := hconc2.min_le_of_mem_Icc (show u2 ∈ Icc u2 1 from ⟨le_rfl, hu2_1⟩)
        (show (1 : ℝ) ∈ Icc u2 1 from ⟨hu2_1, le_rfl⟩) (show u ∈ Icc u2 1 from ⟨hgt2.le, hu1.le⟩)
      have hb := hR1 u2 ⟨hu12, le_rfl⟩
      exact (le_min hb hk1).trans hm

theorem bernD_eq_klN {a u : ℝ} (ha : 0 < a) (ha1 : a < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    LogSum.bernD u a = klN a u / Real.log 2 := by
  unfold LogSum.bernD klN
  rw [Real.log_div hu0.ne' ha.ne', Real.log_div (sub_pos.mpr hu1).ne' (sub_pos.mpr ha1).ne']
  ring

/-- Pointwise kappa-enhanced tangent-gap bound. -/
theorem kappa_tangentGap {a b u v κ : ℝ} (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1)
    (hκa : κ * klN a u ≤ (u - a) ^ 2 / (a * (1 - a)))
    (hκb : κ * klN b v ≤ (v - b) ^ 2 / (b * (1 - b))) :
    κ * ((a - b) ^ 2 / (4 * LogSum.V a b)) * (LogSum.bernD u a + LogSum.bernD v b) ≤
      LogSum.tangentGap a b u v := by
  have hT := LogSum.tangentGap_variance_lower ha hb hu hv
  rw [bernD_eq_klN ha.1 ha.2 hu.1 hu.2, bernD_eq_klN hb.1 hb.2 hv.1 hv.2]
  have hV := LogSum.V_pos ha hb
  have hL := log_two_pos
  have hc : 0 ≤ (a - b) ^ 2 / (4 * LogSum.V a b) / Real.log 2 := by positivity
  calc κ * ((a - b) ^ 2 / (4 * LogSum.V a b)) * (klN a u / Real.log 2 + klN b v / Real.log 2)
      = (a - b) ^ 2 / (4 * LogSum.V a b) / Real.log 2 * (κ * klN a u + κ * klN b v) := by ring
    _ ≤ (a - b) ^ 2 / (4 * LogSum.V a b) / Real.log 2 *
          ((u - a) ^ 2 / (a * (1 - a)) + (v - b) ^ 2 / (b * (1 - b))) :=
        mul_le_mul_of_nonneg_left (add_le_add hκa hκb) hc
    _ = (a - b) ^ 2 / (4 * Real.log 2 * LogSum.V a b) *
          ((u - a) ^ 2 / (a * (1 - a)) + (v - b) ^ 2 / (b * (1 - b))) := by
        field_simp
    _ ≤ LogSum.tangentGap a b u v := hT

/-- **Kappa-enhanced log-sum cost floor** for every finite interior law. -/
theorem kappa_cost_lower_bound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (ha0 : κ * (-Real.log (1 - μ.a)) ≤ μ.a / (1 - μ.a)) (ha1 : κ * (-Real.log μ.a) ≤ (1 - μ.a) / μ.a)
    (hb0 : κ * (-Real.log (1 - μ.b)) ≤ μ.b / (1 - μ.b)) (hb1 : κ * (-Real.log μ.b) ≤ (1 - μ.b) / μ.b) :
    interiorCost μ.a μ.b +
      κ * ((μ.a - μ.b) ^ 2 / (4 * LogSum.V μ.a μ.b)) * ((H μ.a - μ.e) + (H μ.b - μ.f)) ≤ μ.cost := by
  have hpt : ∀ i, κ * ((μ.a - μ.b) ^ 2 / (4 * LogSum.V μ.a μ.b)) *
      (LogSum.bernD (μ.left i) μ.a + LogSum.bernD (μ.right i) μ.b) ≤
      LogSum.tangentGap μ.a μ.b (μ.left i) (μ.right i) := by
    intro i
    exact kappa_tangentGap μ.a_interior μ.b_interior (μ.left_interior i) (μ.right_interior i)
      (kappa_klN μ.a_interior.1 μ.a_interior.2 hκ0 hκ2 ha0 ha1
        (μ.left_interior i).1 (μ.left_interior i).2)
      (kappa_klN μ.b_interior.1 μ.b_interior.2 hκ0 hκ2 hb0 hb1
        (μ.right_interior i).1 (μ.right_interior i).2)
  have h := μ.avg_mono hpt
  have he : μ.avg (fun i => LogSum.bernD (μ.left i) μ.a) = H μ.a - μ.e :=
    LogSum.avg_bernD μ μ.left_interior
  have hf : μ.avg (fun i => LogSum.bernD (μ.right i) μ.b) = H μ.b - μ.f :=
    LogSum.avg_bernD μ μ.right_interior
  rw [LogSum.avg_const_mul, μ.avg_add, he, hf] at h
  have ht : μ.avg (fun i => LogSum.tangentGap μ.a μ.b (μ.left i) (μ.right i)) =
      μ.cost - interiorCost μ.a μ.b := by
    unfold LogSum.tangentGap
    rw [μ.avg_sub, μ.avg_sub, μ.avg_sub, μ.avg_const,
      LogSum.avg_const_mul, LogSum.avg_const_mul, μ.avg_sub, μ.avg_sub, μ.avg_const, μ.avg_const]
    change μ.cost - interiorCost μ.a μ.b - LogSum.gradLeft μ.a μ.b * (μ.a - μ.a) -
      LogSum.gradRight μ.a μ.b * (μ.b - μ.b) = _
    ring
  rw [ht] at h
  linarith

end CKLaneM07

#check @CKLaneM07.kappa_klN
#check @CKLaneM07.kappa_tangentGap
#check @CKLaneM07.kappa_cost_lower_bound
#print axioms CKLaneM07.kappa_klN
#print axioms CKLaneM07.kappa_cost_lower_bound

end


