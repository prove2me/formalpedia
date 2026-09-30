-- Prove2me | Definitions.Def_CK_CKLaneE_SLeaf
-- name    : CK_CKLaneE_SLeaf
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:14:59.739029+00:00
-- url     : https://prove2.me/theorems/e4577b25-0898-4c72-8202-2383c2e449b9
-- title:
--   Courtade–Kumar proof module `CKLaneE.SLeaf` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.SLeaf` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.SLeaf` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.SLeaf (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/SLeaf.lean)

import Definitions.Def_CK_CKLaneE_CertW

-- ===== source module CKLaneE.SLeaf =====
section

/-!
# Lane E: archived same-side (S) leaves, scope-locked form (BRIEF §7)

* `SBox` / `InS` / `LeafS`: the archived box in coordinates `(x, b, t)` with `a = b·2^-x`, `E = t·C0`,
  `C0 = (H a + H b)/2` (real `rpow`), and the leaf semantics
  `∀ k μ, μ.a ≤ μ.b → InS B μ.a μ.b μ.meanEntropy → phi mid E < psi mid E → μ.gap ≤ μ.cost`.
* `sBox p`: exact `COVER.reconstruct` of an archived path from root `[[0,32],[1/32,1/2],[0,1]]`
  (path digit `c = 2·axis + side`, midpoint bisection).
* Refinement trees over the ratio/mean rectangle with log-sum leaves (`LS`, `LS2`, `LS3`) and entropy
  floor `E1 ≤ t0 · CLo(rectangle)`; `leafS_of_check` turns one kernel-checked Boolean (rectangle
  containment of the archived `rpow` ratio interval by certified logarithms + the tree) into `LeafS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.S

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart
open CKLaneE.NLS (H_le_H)

/-- Archived same-side box: `x ∈ [x0, x1]`, `b ∈ [b0, b1]`, `t ∈ [t0, t1]`. -/
structure SBox where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- `InS B a b E := 2^(-x1) ≤ a/b ≤ 2^(-x0) ∧ b0 ≤ b ≤ b1 ∧ t0·C0 ≤ E ≤ t1·C0`. -/
def InS (B : SBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
    (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)

/-- The archived leaf statement (canonical orientation, strict psi-activity). -/
def LeafS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → InS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-! ## Exact path reconstruction -/

def sRoot : SBox := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

def SBox.child (B : SBox) (d : ℕ) : SBox :=
  match d with
  | 0 => { B with x1 := (B.x0 + B.x1) / 2 }
  | 1 => { B with x0 := (B.x0 + B.x1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- Box of an archived path given as its digit list. -/
def sBoxL (l : List ℕ) : SBox := l.foldl SBox.child sRoot

/-- Box of an archived path string (`COVER.reconstruct`). -/
def sBox (p : String) : SBox := sBoxL (p.toList.map fun c => c.toNat - 48)

/-! ## Refinement trees over the (ratio, mean) rectangle -/

structure Box2 where
  r1 : ℚ
  r2 : ℚ
  b1 : ℚ
  b2 : ℚ
  deriving Repr, DecidableEq

def Box2.lower (R : Box2) (ax : ℕ) (c : ℚ) : Box2 :=
  if ax = 0 then { R with r2 := c } else { R with b2 := c }

def Box2.upper (R : Box2) (ax : ℕ) (c : ℚ) : Box2 :=
  if ax = 0 then { R with r1 := c } else { R with b1 := c }

inductive RC
  | ls (vS vI : ℚ)
  | ls2 (v0S v0I v1S v1I : ℚ)
  | ls3 (v0S v0I v1S v1I : ℚ)

def RC.check : RC → Box3 → Bool
  | .ls vS vI, B => LS.check B vS vI
  | .ls2 a b c d, B => LS2.check B a b c d
  | .ls3 a b c d, B => LS3.check B a b c d

theorem RC.sound (c : RC) (B : Box3) (h : c.check B = true) : GoodW B := by
  cases c with
  | ls vS vI => exact LS.check_soundW B vS vI h
  | ls2 a b c d => exact LS2.check_soundW B a b c d h
  | ls3 a b c d => exact LS3.check_soundW B a b c d h

inductive RT
  | leaf (c : RC) (E1 : ℚ)
  | node (ax : ℕ) (v : ℚ) (l r : RT)

/-- Rational lower bound of `C0` on the rectangle. -/
def CLoQ (R : Box2) : ℚ := (Hlo (R.r1 * R.b1) + Hlo R.b1) / 2

def RT.check (t0 : ℚ) : RT → Box2 → Bool
  | .leaf c E1, R =>
      decide (0 < R.r1 ∧ R.r1 ≤ R.r2 ∧ R.r2 ≤ 1 ∧ 0 < R.b1 ∧ R.b1 ≤ R.b2 ∧ R.b2 ≤ 1 / 2) &&
        ptOk (R.r1 * R.b1) && ptOk R.b1 && decide (E1 ≤ t0 * CLoQ R) &&
        c.check ⟨R.r1, R.r2, R.b1, R.b2, E1, 1⟩
  | .node ax v l r, R => l.check t0 (R.lower ax v) && r.check t0 (R.upper ax v)

/-- Rectangle predicate with the archived relative entropy floor `t0·C0`. -/
def GoodR (t0 : ℚ) (R : Box2) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    (R.r1 : ℝ) ≤ μ.a / μ.b → μ.a / μ.b ≤ (R.r2 : ℝ) → (R.b1 : ℝ) ≤ μ.b → μ.b ≤ (R.b2 : ℝ) →
    (t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem meanEntropy_le_one {k : ℕ} (μ : InteriorLaw (Fin k)) : μ.meanEntropy ≤ 1 := by
  unfold InteriorLaw.meanEntropy
  have h1 := μ.e_le_cap
  have h2 := μ.f_le_cap
  have h3 := H_le_one μ.a
  have h4 := H_le_one μ.b
  linarith

theorem leaf_goodR (t0 : ℚ) (ht0 : 0 ≤ t0) (c : RC) (E1 : ℚ) (R : Box2)
    (h : (RT.leaf c E1).check t0 R = true) : GoodR t0 R := by
  simp only [RT.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨q1, q2, q3, q4, q5, q6⟩, hpa⟩, hpb⟩, hE1⟩, hc⟩ := h
  have hG := RC.sound c _ hc
  intro k μ hab hr1 hr2 hb1 hb2 hE hact
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha0 : 0 < μ.a := μ.a_interior.1
  have R1 : (0 : ℝ) < R.r1 := by exact_mod_cast q1
  have B1 : (0 : ℝ) < R.b1 := by exact_mod_cast q4
  have B2 : (R.b2 : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr q6
    push_cast at h; linarith
  have hbh : μ.b ≤ 1 / 2 := hb2.trans B2
  have hah : μ.a ≤ 1 / 2 := by linarith
  have har : μ.a = μ.a / μ.b * μ.b := by field_simp
  have hal : (R.r1 : ℝ) * R.b1 ≤ μ.a := by
    rw [har]; exact mul_le_mul hr1 hb1 B1.le (by positivity)
  obtain ⟨HaL, _⟩ := H_bounds hpa
  obtain ⟨HbL, _⟩ := H_bounds hpb
  push_cast at HaL
  have hHa : ((Hlo (R.r1 * R.b1) : ℚ) : ℝ) ≤ H μ.a :=
    HaL.trans (H_le_H (by positivity) hal hah)
  have hHb : ((Hlo R.b1 : ℚ) : ℝ) ≤ H μ.b := HbL.trans (H_le_H B1.le hb1 hbh)
  have hC : ((CLoQ R : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    simp only [CLoQ]; push_cast; linarith
  have hE1R : ((E1 : ℚ) : ℝ) ≤ (t0 : ℝ) * ((CLoQ R : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hE1
    push_cast at h ⊢; linarith
  have ht0R : (0 : ℝ) ≤ t0 := by exact_mod_cast ht0
  have hmono : (t0 : ℝ) * ((CLoQ R : ℚ) : ℝ) ≤ (t0 : ℝ) * ((H μ.a + H μ.b) / 2) :=
    mul_le_mul_of_nonneg_left hC ht0R
  refine hG k μ hab ⟨hr1, hr2, hb1, hb2, ?_, ?_⟩ hact
  · show ((E1 : ℚ) : ℝ) ≤ μ.meanEntropy
    linarith
  · show μ.meanEntropy ≤ ((1 : ℚ) : ℝ)
    push_cast; exact meanEntropy_le_one μ

theorem Box2.lower_zero (R : Box2) (c : ℚ) : R.lower 0 c = { R with r2 := c } := by
  simp [Box2.lower]
theorem Box2.upper_zero (R : Box2) (c : ℚ) : R.upper 0 c = { R with r1 := c } := by
  simp [Box2.upper]
theorem Box2.lower_ne (R : Box2) {ax : ℕ} (c : ℚ) (h : ax ≠ 0) : R.lower ax c = { R with b2 := c } := by
  simp [Box2.lower, h]
theorem Box2.upper_ne (R : Box2) {ax : ℕ} (c : ℚ) (h : ax ≠ 0) : R.upper ax c = { R with b1 := c } := by
  simp [Box2.upper, h]

theorem RT.sound (t0 : ℚ) (ht0 : 0 ≤ t0) : ∀ (t : RT) (R : Box2), t.check t0 R = true → GoodR t0 R
  | .leaf c E1, R, h => leaf_goodR t0 ht0 c E1 R h
  | .node ax v l r, R, h => by
      simp only [RT.check, Bool.and_eq_true] at h
      have hl := RT.sound t0 ht0 l _ h.1
      have hr := RT.sound t0 ht0 r _ h.2
      intro k μ hab h1 h2 h3 h4 hE hact
      by_cases hax : ax = 0
      · subst hax
        rw [Box2.lower_zero] at hl
        rw [Box2.upper_zero] at hr
        rcases le_total (μ.a / μ.b) (v : ℝ) with hv | hv
        · exact hl k μ hab h1 hv h3 h4 hE hact
        · exact hr k μ hab hv h2 h3 h4 hE hact
      · rw [Box2.lower_ne R v hax] at hl
        rw [Box2.upper_ne R v hax] at hr
        rcases le_total μ.b (v : ℝ) with hv | hv
        · exact hl k μ hab h1 h2 h3 hv hE hact
        · exact hr k μ hab h1 h2 hv h4 hE hact

/-! ## Archived ratio interval inside the rational rectangle -/

theorem r1_le_rpow {r1 x1 : ℚ} (hx : 0 ≤ x1) (hr : 0 < r1) (hr1 : r1 ≤ 1)
    (h : x1 = 0 ∨ (ptOk r1 = true ∧ lHi r1 ≤ -x1 * LqHi)) :
    (r1 : ℝ) ≤ (2 : ℝ) ^ (-(x1 : ℝ)) := by
  rcases h with h | ⟨hp, hl⟩
  · subst h
    simp only [Rat.cast_zero, neg_zero, Real.rpow_zero]
    exact_mod_cast hr1
  · have hrR : (0 : ℝ) < r1 := by exact_mod_cast hr
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(x1 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [← Real.log_le_log_iff hrR h2pos, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    obtain ⟨_, hlog, _, _⟩ := ptOk_sound hp
    obtain ⟨_, hL2⟩ := log_two_mem
    have hlR : ((lHi r1 : ℚ) : ℝ) ≤ -(x1 : ℝ) * ((LqHi : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hl
      push_cast at this; linarith
    have hxR : (0 : ℝ) ≤ x1 := by exact_mod_cast hx
    have : -(x1 : ℝ) * ((LqHi : ℚ) : ℝ) ≤ -(x1 : ℝ) * Real.log 2 := by nlinarith
    linarith

theorem rpow_le_r2 {r2 x0 : ℚ} (hx : 0 ≤ x0)
    (h : (x0 = 0 ∧ r2 = 1) ∨ (ptOk r2 = true ∧ -x0 * LqLo ≤ lLo r2)) :
    (2 : ℝ) ^ (-(x0 : ℝ)) ≤ (r2 : ℝ) := by
  rcases h with ⟨h0, h1⟩ | ⟨hp, hl⟩
  · subst h0; subst h1
    simp
  · have hrR : (0 : ℝ) < r2 := by exact_mod_cast (ptOk_pos hp).1
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(x0 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [← Real.log_le_log_iff h2pos hrR, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    obtain ⟨hlog, _, _, _⟩ := ptOk_sound hp
    obtain ⟨hL1, _⟩ := log_two_mem
    have hlR : -(x0 : ℝ) * ((LqLo : ℚ) : ℝ) ≤ ((lLo r2 : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hl
      push_cast at this; linarith
    have hxR : (0 : ℝ) ≤ x0 := by exact_mod_cast hx
    have : -(x0 : ℝ) * Real.log 2 ≤ -(x0 : ℝ) * ((LqLo : ℚ) : ℝ) := by nlinarith
    linarith

/-- Equal means: the entropy drop vanishes, so the split bound is `0 ≤ cost`. -/
theorem gap_le_cost_of_eq {k : ℕ} (μ : InteriorLaw (Fin k)) (h : μ.a = μ.b)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) : μ.gap ≤ μ.cost := by
  apply μ.gap_le_of_splitBound hact
  have hΔ : μ.entropyDrop = 0 := by
    have e : μ.entropyDrop = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
    rw [e, ← h]
    have : (μ.a + μ.a) / 2 = μ.a := by ring
    rw [this]; ring
  have hsb : μ.splitBound = 0 := by
    have e : μ.splitBound = P (μ.entropyDrop + μ.meanDeficit) - P μ.meanDeficit := rfl
    rw [e, hΔ, zero_add, sub_self]
  rw [hsb]
  have hfl : μ.psiLogSumCostFloor = 0 := by
    unfold InteriorLaw.psiLogSumCostFloor interiorCost
    rw [h]; ring
  have := μ.psiLogSumCostFloor_le_cost
  linarith

/-! ## The archived-leaf bridge -/

def leafCheck (B : SBox) (r1 r2 : ℚ) (t : RT) : Bool :=
  decide (0 ≤ B.x0 ∧ B.x0 ≤ B.x1 ∧ 0 ≤ B.t0 ∧ 0 < r1 ∧ r1 ≤ r2 ∧ r2 ≤ 1) &&
    (decide (B.x1 = 0) || (ptOk r1 && decide (lHi r1 ≤ -B.x1 * LqHi))) &&
    (decide (B.x0 = 0 ∧ r2 = 1) || (ptOk r2 && decide (-B.x0 * LqLo ≤ lLo r2))) &&
    t.check B.t0 ⟨r1, r2, B.b0, B.b1⟩

theorem leafS_of_check (B : SBox) (r1 r2 : ℚ) (t : RT) (h : leafCheck B r1 r2 t = true) :
    LeafS B := by
  simp only [leafCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hx0, hxx, ht0, hr1p, hr12, hr2⟩, hA⟩, hB⟩, ht⟩ := h
  have hG := RT.sound B.t0 ht0 t _ ht
  intro k μ hab hin hact
  obtain ⟨hx1, hx0', hb0, hb1, hE0, _⟩ := hin
  rcases lt_or_eq_of_le hab with hlt | heq
  · refine hG k μ hlt ?_ ?_ hb0 hb1 hE0 hact.le
    · exact (r1_le_rpow (hx0.trans hxx) hr1p (hr12.trans hr2) hA).trans hx1
    · exact hx0'.trans (rpow_le_r2 hx0 hB)
  · exact gap_le_cost_of_eq μ heq hact.le

end CKLaneE.S

#check @CKLaneE.S.leafS_of_check
#print axioms CKLaneE.S.leafS_of_check

end


