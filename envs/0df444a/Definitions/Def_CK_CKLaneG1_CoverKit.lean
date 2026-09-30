-- Prove2me | Definitions.Def_CK_CKLaneG1_CoverKit
-- name    : CK_CKLaneG1_CoverKit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:53:59.489538+00:00
-- url     : https://prove2.me/theorems/fc44929a-270a-48cb-ac07-d565531a80ae
-- title:
--   Courtade–Kumar proof module `CKLaneG1.CoverKit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG1.CoverKit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG1.CoverKit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG1.CoverKit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG1/CoverKit.lean)

import Definitions.Def_CK_CKLaneN1_Tree
import Definitions.Def_CK_CKLaneD_Checker
import Definitions.Def_CK_GeneralCK_BellmanAssembly

-- ===== source module CKLaneG1.CoverKit =====
section

/-!
# Lane G1: shared cover kit for the archived CentralSquare / NO_SEP certificate covers

Built on Lane N1's generic tree kernel `CKLaneN1.Tree` (`PT`, `B3`, `B3.ofPath`, `B3.Mem`, `PT.cover`).
Archived trees carry `ℕ` label codes (`PT ℕ`); a path digit `c` halves axis `c / 2` (lower half for even
`c`), exactly as every archived `reconstruct`.

* `PT.checkB f T B` : Boolean leaf check along the tree carrying the exact box (no leaf list is
  materialised; one halving per node).  `PT.checkB_sound` : every leaf of `T.leaves` passes `f`.
* `PT.nleaves` / `PT.nlabel` : structural leaf counts (`= T.leaves.length`, resp. filtered count).
* `InABT E0 B a b E` : physical image of an `(a, b, t)` box with entropy floor `E0`,
  `E = E0 + t (C0 - E0)`, `C0 = (H a + H b)/2` (entropy split arbitrary).  For `E0 = CKLaneD.EMIN`
  it is Lane D's `InBox` (`inABT_iff_inBox`, `Iff.rfl`).
* `abt_cover` : every interior law with `(a, b)` in the root rectangle and `E0 ≤ E` lies in the image
  of some leaf of any tree over a root with `t ∈ [c0, c1] ⊇ [0, 1]`.
* `InAB B a b` : image of a 2-D mean box (third coordinate unused); `ab_cover`.
-/

set_option autoImplicit false

namespace CKLaneG1

open GeneralCK CKLaneN1

/-! ## Structural Boolean checks and counts -/

/-- Boolean leaf check carrying the exact box of each node. -/
def PT.checkB (f : B3 → ℕ → Bool) : PT ℕ → B3 → Bool
  | .leaf l, B => f B l
  | .node ax l r, B => PT.checkB f l (B.step (2 * ax)) && PT.checkB f r (B.step (2 * ax + 1))

theorem PT.checkB_soundR (f : B3 → ℕ → Bool) (R : B3) :
    ∀ (T : PT ℕ) (rpre : List ℕ), PT.checkB f T (R.ofPath rpre.reverse) = true →
      ∀ q ∈ T.leavesR rpre, f (R.ofPath q.1) q.2 = true
  | .leaf l, rpre, h, q, hq => by
      simp only [PT.leavesR, List.mem_singleton] at hq
      subst hq
      exact h
  | .node ax l r, rpre, h, q, hq => by
      simp only [PT.checkB, Bool.and_eq_true] at h
      simp only [PT.leavesR, List.mem_append] at hq
      rcases hq with hq | hq
      · have hl : PT.checkB f l (R.ofPath (2 * ax :: rpre).reverse) = true := by
          rw [List.reverse_cons, B3.ofPath_append]; exact h.1
        exact PT.checkB_soundR f R l (2 * ax :: rpre) hl q hq
      · have hr : PT.checkB f r (R.ofPath ((2 * ax + 1) :: rpre).reverse) = true := by
          rw [List.reverse_cons, B3.ofPath_append]; exact h.2
        exact PT.checkB_soundR f R r ((2 * ax + 1) :: rpre) hr q hq

theorem PT.checkB_sound (f : B3 → ℕ → Bool) (R : B3) (T : PT ℕ) (h : PT.checkB f T R = true) :
    ∀ q ∈ T.leaves, f (R.ofPath q.1) q.2 = true :=
  PT.checkB_soundR f R T [] h

/-- Number of leaves. -/
def PT.nleaves : PT ℕ → ℕ
  | .leaf _ => 1
  | .node _ l r => PT.nleaves l + PT.nleaves r

/-- Number of leaves with label `c`. -/
def PT.nlabel (c : ℕ) : PT ℕ → ℕ
  | .leaf l => if l = c then 1 else 0
  | .node _ l r => PT.nlabel c l + PT.nlabel c r

theorem PT.length_leavesR : ∀ (T : PT ℕ) (rpre : List ℕ), (T.leavesR rpre).length = PT.nleaves T
  | .leaf _, _ => by simp [PT.leavesR, PT.nleaves]
  | .node _ l r, rpre => by
      simp only [PT.leavesR, List.length_append, PT.nleaves]
      rw [PT.length_leavesR l, PT.length_leavesR r]

theorem PT.length_leaves (T : PT ℕ) : T.leaves.length = PT.nleaves T := PT.length_leavesR T []

/-! ## `(a, b, t)` boxes with entropy floor `E0` -/

/-- Physical image of an `(a, b, t)` box: `E = E0 + t (C0 - E0)`, `C0 = (H a + H b)/2`. -/
def InABT (E0 : ℚ) (B : B3) (a b E : ℝ) : Prop :=
  (B.a0 : ℝ) ≤ a ∧ a ≤ (B.a1 : ℝ) ∧ (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (E0 : ℝ) + (B.c0 : ℝ) * ((H a + H b) / 2 - (E0 : ℝ)) ≤ E ∧
    E ≤ (E0 : ℝ) + (B.c1 : ℝ) * ((H a + H b) / 2 - (E0 : ℝ))

/-- Lane D box with the same coordinates. -/
def B3.toDBox (B : B3) : CKLaneD.Box := ⟨B.a0, B.a1, B.b0, B.b1, B.c0, B.c1⟩

/-- For `E0 = CKLaneD.EMIN` the image is Lane D's `InBox`. -/
theorem inABT_iff_inBox (B : B3) (a b E : ℝ) :
    InABT CKLaneD.EMIN B a b E ↔ CKLaneD.InBox (B3.toDBox B) a b E := Iff.rfl

theorem inABT_of_mem {E0 : ℚ} {B : B3} {a b E t : ℝ} (h : B.Mem a b t)
    (hE : E = (E0 : ℝ) + t * ((H a + H b) / 2 - (E0 : ℝ)))
    (hC : (E0 : ℝ) ≤ (H a + H b) / 2) : InABT E0 B a b E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hC' : 0 ≤ (H a + H b) / 2 - (E0 : ℝ) := by linarith
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [hE]; nlinarith [mul_le_mul_of_nonneg_right h5 hC']
  · rw [hE]; nlinarith [mul_le_mul_of_nonneg_right h6 hC']

/-- Coverage: every interior law with `(a, b)` in the root rectangle and `E0 ≤ E` lies in the image
of some leaf (any tree; root `t`-range must contain `[0, 1]`). -/
theorem abt_cover (E0 : ℚ) (R : B3) (T : PT ℕ) {k : ℕ} (μ : InteriorLaw (Fin k))
    (ha0 : (R.a0 : ℝ) ≤ μ.a) (ha1 : μ.a ≤ (R.a1 : ℝ)) (hb0 : (R.b0 : ℝ) ≤ μ.b)
    (hb1 : μ.b ≤ (R.b1 : ℝ)) (hc0 : R.c0 ≤ 0) (hc1 : 1 ≤ R.c1)
    (hE : (E0 : ℝ) ≤ μ.meanEntropy) :
    ∃ q ∈ T.leaves, InABT E0 (R.ofPath q.1) μ.a μ.b μ.meanEntropy := by
  have hEle : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap]
  set C := (H μ.a + H μ.b) / 2 with hCdef
  set t : ℝ := if (E0 : ℝ) < C then (μ.meanEntropy - E0) / (C - E0) else 0 with ht
  have htE : μ.meanEntropy = (E0 : ℝ) + t * (C - E0) := by
    rw [ht]
    split_ifs with hc
    · have hne : C - (E0 : ℝ) ≠ 0 := (sub_pos.mpr hc).ne'
      rw [div_mul_cancel₀ _ hne]
      ring
    · have : C = (E0 : ℝ) := by linarith
      rw [this]; ring_nf; linarith
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rw [ht]
    split_ifs with hc
    · constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    · norm_num
  have hc0' : (R.c0 : ℝ) ≤ 0 := by exact_mod_cast hc0
  have hc1' : (1 : ℝ) ≤ (R.c1 : ℝ) := by exact_mod_cast hc1
  have hroot : R.Mem μ.a μ.b t :=
    ⟨ha0, ha1, hb0, hb1, by linarith [ht01.1], by linarith [ht01.2]⟩
  obtain ⟨q, hq, hq'⟩ := PT.cover R T hroot
  exact ⟨q, hq, inABT_of_mem hq' (by rw [← hCdef]; exact htE) (by rw [← hCdef]; linarith)⟩

/-! ## 2-D mean boxes -/

/-- Physical image of a 2-D mean box (third coordinate unused). -/
def InAB (B : B3) (a b : ℝ) : Prop :=
  (B.a0 : ℝ) ≤ a ∧ a ≤ (B.a1 : ℝ) ∧ (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ)

theorem ab_cover (R : B3) (T : PT ℕ) {a b : ℝ} (ha0 : (R.a0 : ℝ) ≤ a) (ha1 : a ≤ (R.a1 : ℝ))
    (hb0 : (R.b0 : ℝ) ≤ b) (hb1 : b ≤ (R.b1 : ℝ)) (hc : R.c0 ≤ R.c1) :
    ∃ q ∈ T.leaves, InAB (R.ofPath q.1) a b := by
  have hc' : (R.c0 : ℝ) ≤ (R.c1 : ℝ) := by exact_mod_cast hc
  obtain ⟨q, hq, hq'⟩ := PT.cover R T (x := a) (y := b) (z := (R.c0 : ℝ))
    ⟨ha0, ha1, hb0, hb1, le_refl _, hc'⟩
  exact ⟨q, hq, hq'.1, hq'.2.1, hq'.2.2.1, hq'.2.2.2.1⟩

/-! ## Separation (`outside`) certificates: `b1 - a0 < D` on the box -/

/-- Leaf check for `outside` label `c`: the box has `b1 - a0 < D`. -/
def sepOK (c : ℕ) (D : ℚ) (B : B3) (l : ℕ) : Bool := l != c || decide (B.b1 - B.a0 < D)

theorem sep_of_check {c : ℕ} {D : ℚ} {B : B3} {l : ℕ} (h : sepOK c D B l = true) (hl : l = c)
    {a b : ℝ} (ha : (B.a0 : ℝ) ≤ a) (hb : b ≤ (B.b1 : ℝ)) : b - a < (D : ℝ) := by
  subst hl
  simp only [sepOK, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at h
  have h' : ((B.b1 - B.a0 : ℚ) : ℝ) < (D : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- Every `outside` leaf (label `c`) of a checked `(a,b,t)` tree has `b - a < D` on its image. -/
theorem abt_outside {E0 : ℚ} {R : B3} {T : PT ℕ} {c : ℕ} {D : ℚ}
    (h : PT.checkB (sepOK c D) T R = true) :
    ∀ q ∈ T.leaves, q.2 = c → ∀ a b E : ℝ, InABT E0 (R.ofPath q.1) a b E → b - a < (D : ℝ) := by
  intro q hq hl a b E hin
  exact sep_of_check (PT.checkB_sound _ R T h q hq) hl hin.1 hin.2.2.2.1

/-! ## Mirror certificates (2-D): the box lies in `b ≤ a` -/

/-- Leaf check for `mirror` label `c`: `b1 ≤ a0` on the box. -/
def mirOK (c : ℕ) (B : B3) (l : ℕ) : Bool := l != c || decide (B.b1 ≤ B.a0)

theorem ab_mirror {R : B3} {T : PT ℕ} {c : ℕ} (h : PT.checkB (mirOK c) T R = true) :
    ∀ q ∈ T.leaves, q.2 = c → ∀ a b : ℝ, InAB (R.ofPath q.1) a b → b ≤ a := by
  intro q hq hl a b hin
  have hc := PT.checkB_sound _ R T h q hq
  rw [hl] at hc
  simp only [mirOK, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hc
  have hc' : (((R.ofPath q.1).b1 : ℚ) : ℝ) ≤ (((R.ofPath q.1).a0 : ℚ) : ℝ) := by exact_mod_cast hc
  obtain ⟨h1, _, _, h4⟩ := hin
  linarith

end CKLaneG1

#check @CKLaneG1.PT.checkB_sound
#print axioms CKLaneG1.PT.checkB_sound
#check @CKLaneG1.abt_cover
#print axioms CKLaneG1.abt_cover
#check @CKLaneG1.abt_outside
#print axioms CKLaneG1.abt_outside
#check @CKLaneG1.ab_cover
#print axioms CKLaneG1.ab_cover
#check @CKLaneG1.inABT_iff_inBox

end


