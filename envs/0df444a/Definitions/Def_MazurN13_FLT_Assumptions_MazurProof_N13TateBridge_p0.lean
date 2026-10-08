-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TateBridge_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TateBridge_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:46:20.791905+00:00
-- url     : https://prove2.me/theorems/28c6e666-2502-446c-a1ed-809c5624243c
-- title:
--   FLT.Assumptions.MazurProof.N13TateBridge source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TateBridge

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TateBridge
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNFDivision_p0

set_option autoImplicit false




/-!
# The Tate-normal-form bridge to the optimized model of `X₁(13)`

This file isolates the birational geometry in the order-13 argument.  The
high-degree Tate division factor is first reduced, by Kubert's standard
substitution

`b = r s (r - 1)`, `c = s (r - 1)`,

to a low-degree plane model.  A second birational map sends its
nondegenerate locus to the optimized genus-two model

`y² + (x³ + x² + 1)y = x² + x`.

All identities below are identities of rational functions.  No rational-point
classification is used here.
-/

namespace MazurProof.N13TateBridge

/-- Kubert's raw affine equation for `X₁(13)`. -/
def rawF13 (r s : ℚ) : ℚ :=
  r ^ 3 - r ^ 2 * s ^ 4 + 5 * r ^ 2 * s ^ 3 - 9 * r ^ 2 * s ^ 2
    + 4 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 3 + 6 * r * s ^ 2
    - 3 * r * s + r - s ^ 3

/-- The optimized affine genus-two model of `X₁(13)`. -/
def C13OptEq (x y : ℚ) : Prop :=
  y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y = x ^ 2 + x

/-- A convenient affine open avoiding all four affine rational cusps. -/
def OptNonCusp13 (x y : ℚ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ y + 1 ≠ 0

/-- The nondegenerate part of Kubert's raw affine chart. -/
def RawNondegenerate13 (r s : ℚ) : Prop :=
  r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ s ≠ r

/-- The two-step Kubert substitution factors the Tate division condition. -/
theorem tateF13_substitution (r s : ℚ) :
    TateNFDivision.F13 (r * s * (r - 1)) (s * (r - 1)) =
      -s ^ 7 * (r - 1) ^ 11 * rawF13 r s := by
  simp only [TateNFDivision.F13, TateNFDivision.F8, rawF13]
  ring

theorem rawF13_at_s_one (r : ℚ) :
    rawF13 r 1 = (r - 1) ^ 3 := by
  simp [rawF13]
  ring

theorem rawF13_at_diagonal (r : ℚ) :
    rawF13 r r = -r * (r - 1) ^ 5 := by
  simp [rawF13]
  ring

/-- A nonzero Tate solution gives a point on the nondegenerate raw chart. -/
theorem raw_point_of_tateF13
    {b c : ℚ} (hb : b ≠ 0) (hF : TateNFDivision.F13 b c = 0) :
    ∃ r s : ℚ,
      rawF13 r s = 0 ∧ RawNondegenerate13 r s ∧
        b = r * s * (r - 1) ∧ c = s * (r - 1) := by
  have hc : c ≠ 0 := by
    intro hc
    subst c
    apply (pow_ne_zero 7 hb)
    rw [TateNFDivision.F13, TateNFDivision.F8] at hF
    ring_nf at hF ⊢
    exact neg_eq_zero.mp hF
  have hbc : b ≠ c := by
    intro hbc
    subst c
    apply (pow_ne_zero 11 hb)
    rw [TateNFDivision.F13, TateNFDivision.F8] at hF
    ring_nf at hF ⊢
    exact hF
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hr0 : r ≠ 0 := by
    exact div_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    intro hr
    apply hbc
    apply (div_eq_one_iff_eq hc).mp
    exact hr
  have hs0 : s ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)
  have hb_param : b = r * s * (r - 1) := by
    dsimp [r, s]
    field_simp
  have hc_param : c = s * (r - 1) := by
    dsimp [r, s]
    field_simp
  have hraw : rawF13 r s = 0 := by
    have hfactor :
        -s ^ 7 * (r - 1) ^ 11 * rawF13 r s = 0 := by
      rw [← tateF13_substitution, ← hb_param, ← hc_param, hF]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero
        (neg_ne_zero.mpr (pow_ne_zero 7 hs0))
        (pow_ne_zero 11 (sub_ne_zero.mpr hr1)))
  have hs1 : s ≠ 1 := by
    intro hs
    have hpow : (r - 1) ^ 3 = 0 := by
      rw [← rawF13_at_s_one]
      simpa [hs] using hraw
    exact (pow_ne_zero 3 (sub_ne_zero.mpr hr1)) hpow
  have hsr : s ≠ r := by
    intro hs
    have hzero : -r * (r - 1) ^ 5 = 0 := by
      rw [← rawF13_at_diagonal]
      simpa [hs] using hraw
    exact (mul_ne_zero
      (neg_ne_zero.mpr hr0)
      (pow_ne_zero 5 (sub_ne_zero.mpr hr1))) hzero
  exact ⟨r, s, hraw, ⟨hr0, hr1, hs0, hs1, hsr⟩, hb_param, hc_param⟩

/-- The inverse birational map from the raw chart to the optimized model. -/
def rawToOptX (r s : ℚ) : ℚ :=
  (1 - r) * (1 - s) / (s - r)

/-- The second coordinate of the inverse birational map. -/
def rawToOptY (r s : ℚ) : ℚ :=
  (s - r) / (1 - s)

/-- The raw-to-optimized map lands on the optimized genus-two equation. -/
theorem rawToOpt_mem
    {r s : ℚ} (hraw : rawF13 r s = 0)
    (hs1 : s ≠ 1) (hsr : s ≠ r) :
    C13OptEq (rawToOptX r s) (rawToOptY r s) := by
  unfold C13OptEq rawToOptX rawToOptY
  field_simp [sub_ne_zero.mpr hsr, sub_ne_zero.mpr (Ne.symm hs1)]
  unfold rawF13 at hraw
  linear_combination (r - 1) * hraw

/-- On the nondegenerate chart the optimized point maps back to `(r,s)`. -/
theorem optToRaw_roundtrip
    {r s : ℚ} (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hsr : s ≠ r) :
    let x := rawToOptX r s
    let y := rawToOptY r s
    r = 1 - x * y ∧ s = 1 - x * y / (y + 1) := by
  dsimp [rawToOptX, rawToOptY]
  have hrs : s - r ≠ 0 := sub_ne_zero.mpr hsr
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hxy :
      ((1 - r) * (1 - s) / (s - r)) * ((s - r) / (1 - s)) =
        1 - r := by
    field_simp [hrs, h1s]
  have hyone :
      (s - r) / (1 - s) + 1 = (1 - r) / (1 - s) := by
    field_simp [h1s]
    ring
  constructor
  · rw [hxy]
    ring
  · rw [hxy, hyone]
    field_simp [h1r, h1s]
    ring

/-- A nondegenerate raw point maps away from all affine rational cusps. -/
theorem rawToOpt_noncusp
    {r s : ℚ} (hnd : RawNondegenerate13 r s) :
    OptNonCusp13 (rawToOptX r s) (rawToOptY r s) := by
  rcases hnd with ⟨_, hr1, _, hs1, hsr⟩
  have hrs : s - r ≠ 0 := sub_ne_zero.mpr hsr
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  constructor
  · exact div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hr1))
        (sub_ne_zero.mpr (Ne.symm hs1)))
      hrs
  constructor
  · exact div_ne_zero hrs h1s
  · unfold rawToOptY
    have hyone :
        (s - r) / (1 - s) + 1 = (1 - r) / (1 - s) := by
      field_simp [h1s]
      ring
    rw [hyone]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hr1)) h1s

/-- The complete Tate-to-optimized-model bridge for order 13. -/
theorem exists_C13Opt_point_of_tateF13
    {b c : ℚ} (hb : b ≠ 0) (hF : TateNFDivision.F13 b c = 0) :
    ∃ x y : ℚ, C13OptEq x y ∧ OptNonCusp13 x y := by
  obtain ⟨r, s, hraw, hnd, _, _⟩ := raw_point_of_tateF13 hb hF
  exact ⟨rawToOptX r s, rawToOptY r s,
    rawToOpt_mem hraw hnd.2.2.2.1 hnd.2.2.2.2,
    rawToOpt_noncusp hnd⟩

end MazurProof.N13TateBridge


