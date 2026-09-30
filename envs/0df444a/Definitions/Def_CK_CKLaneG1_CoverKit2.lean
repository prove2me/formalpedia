-- Prove2me | Definitions.Def_CK_CKLaneG1_CoverKit2
-- name    : CK_CKLaneG1_CoverKit2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:56:43.380182+00:00
-- url     : https://prove2.me/theorems/ab2f0306-dd0b-4d2a-a1e2-29eda89aa60c
-- title:
--   Courtade–Kumar proof module `CKLaneG1.CoverKit2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG1.CoverKit2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG1.CoverKit2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG1.CoverKit2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG1/CoverKit2.lean)

import Definitions.Def_CK_CKLaneG1_CoverKit

-- ===== source module CKLaneG1.CoverKit2 =====
section

/-!
# Lane G1: cover kit, part 2 — `(E, x, y)` boxes (OPP transition theorem (4))

Archive `CK_OPPOSITE_EXTENSION/transition/TRANSITION.py`: after label exchange and simultaneous
complement `a ≤ b`, `a + b ≤ 1`; with `d = b - a`, `q = 1 - a - b`, `x = d/E`, `y = q/E`
(`a = [1 - (x+y)E]/2`, `b = [1 + (x-y)E]/2`).

* `InExy B a b E` : image of an `(E, x, y)` box (axes: `a*` = E, `b*` = x, `c*` = y) —
  definitionally `B.Mem E ((b-a)/E) ((1-a-b)/E)`.  `exy_cover` (any tree).
* `exy_mem_root` : the transition domain (`a + b ≤ 1`, `1/2 ≤ b`, `1/50 ≤ b - a`, `E ≤ 11/200`,
  `4E ≤ b - a ≤ 8E`) lies in the archived root `[1/400,11/200] × [4,8] × [0,8]`.
* `exy_outside` : the archived `outside` rule (`y0 > x1`, or `(x0+y0) E0 > 4/5`, or `x1 E1 < 1/50`)
  refutes `q ≤ d`, `1/10 ≤ a` (i.e. `q + d ≤ 4/5`), `1/50 ≤ d` on the whole leaf image.
* `exy_collar` : the archived `prior_collar` rule (`y1 ≤ 1 ∧ x0 ≥ 5`, `y1 ≤ 2 ∧ x0 ≥ 6`,
  `y1 ≤ 4 ∧ x0 ≥ 8`) places the whole leaf image in the corresponding collar.
-/

set_option autoImplicit false

namespace CKLaneG1

open GeneralCK CKLaneN1

/-! ## `(E, x, y)` boxes -/

/-- Physical image of an `(E, x, y)` box (`x = (b-a)/E`, `y = (1-a-b)/E`). -/
def InExy (B : B3) (a b E : ℝ) : Prop := B.Mem E ((b - a) / E) ((1 - a - b) / E)

theorem exy_cover (R : B3) (T : PT ℕ) {a b E : ℝ} (hE0 : (R.a0 : ℝ) ≤ E) (hE1 : E ≤ (R.a1 : ℝ))
    (hx0 : (R.b0 : ℝ) ≤ (b - a) / E) (hx1 : (b - a) / E ≤ (R.b1 : ℝ))
    (hy0 : (R.c0 : ℝ) ≤ (1 - a - b) / E) (hy1 : (1 - a - b) / E ≤ (R.c1 : ℝ)) :
    ∃ q ∈ T.leaves, InExy (R.ofPath q.1) a b E :=
  PT.cover R T ⟨hE0, hE1, hx0, hx1, hy0, hy1⟩

/-- The transition domain lies in the archived root `[1/400,11/200] × [4,8] × [0,8]`. -/
theorem exy_mem_root {a b E : ℝ} (hsum : a + b ≤ 1) (hb : 1 / 2 ≤ b) (hd : 1 / 50 ≤ b - a)
    (hE1 : E ≤ 11 / 200) (h4 : 4 * E ≤ b - a) (h8 : b - a ≤ 8 * E) :
    (1 / 400 : ℝ) ≤ E ∧ E ≤ 11 / 200 ∧ (4 : ℝ) ≤ (b - a) / E ∧ (b - a) / E ≤ 8 ∧
      (0 : ℝ) ≤ (1 - a - b) / E ∧ (1 - a - b) / E ≤ 8 := by
  have hEpos : 0 < E := by linarith
  refine ⟨by linarith, hE1, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hEpos]; linarith
  · rw [div_le_iff₀ hEpos]; linarith
  · exact div_nonneg (by linarith) hEpos.le
  · rw [div_le_iff₀ hEpos]; linarith

/-- Leaf check for the transition `outside` label `c`. -/
def trOutOK (c : ℕ) (B : B3) (l : ℕ) : Bool :=
  l != c || (decide (0 ≤ B.a0) && decide (0 ≤ B.b0) && decide (0 ≤ B.c0) &&
    (decide (B.b1 < B.c0) || decide (4 / 5 < (B.b0 + B.c0) * B.a0) || decide (B.b1 * B.a1 < 1 / 50)))

theorem exy_outside_of_check {c : ℕ} {B : B3} {l : ℕ} (h : trOutOK c B l = true) (hl : l = c)
    {a b E : ℝ} (hin : InExy B a b E) (hE : 0 < E) :
    ¬ (1 - a - b ≤ b - a ∧ 1 / 10 ≤ a ∧ 1 / 50 ≤ b - a) := by
  rintro ⟨hqd, ha, hd⟩
  subst hl
  simp only [trOutOK, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hE0, hx0⟩, hy0⟩, hc⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  have hE0' : (0 : ℝ) ≤ (B.a0 : ℝ) := by exact_mod_cast hE0
  have hx0' : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast hx0
  have hy0' : (0 : ℝ) ≤ (B.c0 : ℝ) := by exact_mod_cast hy0
  have hEne : E ≠ 0 := hE.ne'
  have hdx : (b - a) / E * E = b - a := div_mul_cancel₀ (b - a) hEne
  have hqy : (1 - a - b) / E * E = 1 - a - b := div_mul_cancel₀ (1 - a - b) hEne
  set x := (b - a) / E with hxdef
  set y := (1 - a - b) / E with hydef
  rcases hc with (hc | hc) | hc
  · -- y > x on the whole box
    have hc' : (B.b1 : ℝ) < (B.c0 : ℝ) := by exact_mod_cast hc
    have hyx : x < y := by linarith
    have : x * E < y * E := mul_lt_mul_of_pos_right hyx hE
    linarith
  · -- (x + y) E > 4/5 on the whole box
    have hc' : (4 / 5 : ℝ) < ((B.b0 : ℝ) + (B.c0 : ℝ)) * (B.a0 : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hc
      push_cast at h
      exact h
    have hxy : (B.b0 : ℝ) + (B.c0 : ℝ) ≤ x + y := by linarith
    have hm : ((B.b0 : ℝ) + (B.c0 : ℝ)) * (B.a0 : ℝ) ≤ (x + y) * E :=
      mul_le_mul hxy h1 hE0' (by linarith)
    have hsum : (x + y) * E = x * E + y * E := by ring
    linarith
  · -- x E < 1/50 on the whole box
    have hc' : (B.b1 : ℝ) * (B.a1 : ℝ) < 1 / 50 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hc
      push_cast at h
      exact h
    have hm : x * E ≤ (B.b1 : ℝ) * (B.a1 : ℝ) :=
      mul_le_mul h4 h2 hE.le (by linarith)
    linarith

/-- Every archived transition `outside` leaf is irrelevant to the constrained mean domain. -/
theorem exy_outside {R : B3} {T : PT ℕ} {c : ℕ} (h : PT.checkB (trOutOK c) T R = true) :
    ∀ q ∈ T.leaves, q.2 = c → ∀ a b E : ℝ, InExy (R.ofPath q.1) a b E → 0 < E →
      ¬ (1 - a - b ≤ b - a ∧ 1 / 10 ≤ a ∧ 1 / 50 ≤ b - a) := by
  intro q hq hl a b E hin hE
  exact exy_outside_of_check (PT.checkB_sound _ R T h q hq) hl hin hE

/-- Leaf check for the transition `prior_collar` label `c`. -/
def trCollarOK (c : ℕ) (B : B3) (l : ℕ) : Bool :=
  l != c || ((decide (B.c1 ≤ 1) && decide (5 ≤ B.b0)) || (decide (B.c1 ≤ 2) && decide (6 ≤ B.b0)) ||
    (decide (B.c1 ≤ 4) && decide (8 ≤ B.b0)))

theorem exy_collar_of_check {c : ℕ} {B : B3} {l : ℕ} (h : trCollarOK c B l = true) (hl : l = c)
    {a b E : ℝ} (hin : InExy B a b E) (hE : 0 < E) :
    (1 - a - b ≤ E ∧ 5 * E ≤ b - a) ∨ (1 - a - b ≤ 2 * E ∧ 6 * E ≤ b - a) ∨
      (1 - a - b ≤ 4 * E ∧ 8 * E ≤ b - a) := by
  subst hl
  simp only [trCollarOK, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨_, _, h3, _, _, h6⟩ := hin
  have hEne : E ≠ 0 := hE.ne'
  have hdx : (b - a) / E * E = b - a := div_mul_cancel₀ (b - a) hEne
  have hqy : (1 - a - b) / E * E = 1 - a - b := div_mul_cancel₀ (1 - a - b) hEne
  set x := (b - a) / E with hxdef
  set y := (1 - a - b) / E with hydef
  rcases h with (⟨hc, hx⟩ | ⟨hc, hx⟩) | ⟨hc, hx⟩
  · left
    have hc' : ((B.c1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hc
    have hx' : (5 : ℝ) ≤ ((B.b0 : ℚ) : ℝ) := by exact_mod_cast hx
    have hy1 : y ≤ 1 := le_trans h6 hc'
    have hxl : 5 ≤ x := le_trans hx' h3
    have m1 := mul_le_mul_of_nonneg_right hy1 hE.le
    have m2 := mul_le_mul_of_nonneg_right hxl hE.le
    constructor <;> linarith
  · right; left
    have hc' : ((B.c1 : ℚ) : ℝ) ≤ 2 := by exact_mod_cast hc
    have hx' : (6 : ℝ) ≤ ((B.b0 : ℚ) : ℝ) := by exact_mod_cast hx
    have hy1 : y ≤ 2 := le_trans h6 hc'
    have hxl : 6 ≤ x := le_trans hx' h3
    have m1 := mul_le_mul_of_nonneg_right hy1 hE.le
    have m2 := mul_le_mul_of_nonneg_right hxl hE.le
    constructor <;> linarith
  · right; right
    have hc' : ((B.c1 : ℚ) : ℝ) ≤ 4 := by exact_mod_cast hc
    have hx' : (8 : ℝ) ≤ ((B.b0 : ℚ) : ℝ) := by exact_mod_cast hx
    have hy1 : y ≤ 4 := le_trans h6 hc'
    have hxl : 8 ≤ x := le_trans hx' h3
    have m1 := mul_le_mul_of_nonneg_right hy1 hE.le
    have m2 := mul_le_mul_of_nonneg_right hxl hE.le
    constructor <;> linarith

/-- Every archived transition `prior_collar` leaf lies in one of the three archived collars. -/
theorem exy_collar {R : B3} {T : PT ℕ} {c : ℕ} (h : PT.checkB (trCollarOK c) T R = true) :
    ∀ q ∈ T.leaves, q.2 = c → ∀ a b E : ℝ, InExy (R.ofPath q.1) a b E → 0 < E →
      (1 - a - b ≤ E ∧ 5 * E ≤ b - a) ∨ (1 - a - b ≤ 2 * E ∧ 6 * E ≤ b - a) ∨
        (1 - a - b ≤ 4 * E ∧ 8 * E ≤ b - a) := by
  intro q hq hl a b E hin hE
  exact exy_collar_of_check (PT.checkB_sound _ R T h q hq) hl hin hE

end CKLaneG1

#check @CKLaneG1.exy_cover
#print axioms CKLaneG1.exy_cover
#check @CKLaneG1.exy_mem_root
#print axioms CKLaneG1.exy_mem_root
#check @CKLaneG1.exy_outside
#print axioms CKLaneG1.exy_outside
#check @CKLaneG1.exy_collar
#print axioms CKLaneG1.exy_collar

end


