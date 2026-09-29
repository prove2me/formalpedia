-- Prove2me | Definitions.Def_CK_CKLaneG3_SCover
-- name    : CK_CKLaneG3_SCover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:54:22.628983+00:00
-- url     : https://prove2.me/theorems/d56136b6-25b3-4003-86e0-043c2426f1b0
-- title:
--   Courtade–Kumar proof module `CKLaneG3.SCover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.SCover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.SCover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.SCover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/SCover.lean)

import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_EqualMean

-- ===== source module CKLaneG3.SCover =====
section

/-!
# Lane G3: canonical same-side (S) cover definitions (BRIEF §7, route row `SS_Compact`)

Archived same-side cover `same_side/ADAPT_RESULT.json` (sha256 b134020b…e9c8): root
`(x, b, t) ∈ [0,32] × [1/32,1/2] × [0,1]`, coordinate map `a = b·2^-x`, `E = t·C0`,
`C0 = (H a + H b)/2`, exact midpoint halving `same_side/COVER.py reconstruct` (digit `d = 2·axis + side`,
side 0 = lower half, axes `0 = x`, `1 = b`, `2 = t`; `INTERVAL_BASE.split`).

* `SBox` (fields `x0 x1 b0 b1 t0 t1 : ℚ`), `sRoot`, `sStep`, `sBox` : exact archived leaf boxes.
* `InS B a b E` : the physical image of a box, the flat conjunction
  `2^(-x1) ≤ a/b ∧ a/b ≤ 2^(-x0) ∧ b0 ≤ b ∧ b ≤ b1 ∧ t0*C0 ≤ E ∧ E ≤ t1*C0` (real rpow),
  field-for-field identical to the lane-local copies in `CKLaneG1.SExcl`, `CKLaneM06.SForm`,
  `CKLaneE.SLeaf`, `CKLaneM03.Kernel` (`InSBox`, renamed fields), `CKLaneM07.Checker` (renamed fields).
* `SLeafOK B` : the `SS_Compact` per-leaf obligation (canonical orientation, strict psi activity).
* `SSCompactRow` / `CentralSquareRow` : verbatim copies of `CKRoute.SS_Compact` / `CKRoute.CentralSquare`
  (with a verbatim local copy of `CKRoute.PsiActive`), so the coordinator binds them by `Iff.rfl`.
* `inS_step` : the two halves of a halving step cover the image of the parent box (no side conditions).
* `inS_sRoot` : every law of the `SS_Compact` row lies in the image of the root box.
* Adapters to `SLeafOK`: psi-candidate statement, owner forms (`a ≤ b` or strict `a < b`, the latter
  completed at `a = b` by `InteriorLaw.equal_mean_hybrid`), parent dominance, central boxes
  (`1/10 ≤ a` on the box + `CentralSquareRow`), small-mean boxes (`a + b ≤ 1/16` on the box).
-/

set_option autoImplicit false

namespace CKLaneG3

open GeneralCK

/-! ## Boxes -/

/-- An archived same-side box in `(x, b, t)` coordinates. -/
structure SBox where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- Root of the archived same-side cover. -/
def sRoot : SBox := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step of `COVER.reconstruct` (digit `2 * axis + side`). -/
def sStep (B : SBox) (d : ℕ) : SBox :=
  match d with
  | 0 => { B with x1 := (B.x0 + B.x1) / 2 }
  | 1 => { B with x0 := (B.x0 + B.x1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- The exact box of an archived path. -/
def sBox (p : List ℕ) : SBox := p.foldl sStep sRoot

/-- Physical image of an (S) box (BRIEF §7 `InS`). -/
def InS (B : SBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
    (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)

theorem sBox_nil : sBox [] = sRoot := rfl

theorem sBox_append (p : List ℕ) (d : ℕ) : sBox (p ++ [d]) = sStep (sBox p) d := by
  unfold sBox
  rw [List.foldl_append]
  rfl

/-- Transport of a lane-local copy of the box recursion: any map `f` from a lane-local box type
commuting with the root and the halving step sends the lane's `foldl` boxes to `sBox`. -/
theorem sBox_of_commute {α : Type} (stepα : α → ℕ → α) (rootα : α) (f : α → SBox)
    (hroot : f rootα = sRoot) (hstep : ∀ X d, f (stepα X d) = sStep (f X) d) (p : List ℕ) :
    f (p.foldl stepα rootα) = sBox p := by
  unfold sBox
  rw [← hroot]
  clear hroot
  induction p generalizing rootα with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [← hstep]
      exact ih (stepα rootα d)

/-! ## The halving split covers the parent image -/

theorem inS_step (B : SBox) (ax : ℕ) {a b E : ℝ} (h : InS B a b E) :
    InS (sStep B (2 * ax)) a b E ∨ InS (sStep B (2 * ax + 1)) a b E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases ax with _ | _ | _ | ax
  · rcases le_total ((2 : ℝ) ^ (-(((B.x0 + B.x1) / 2 : ℚ) : ℝ))) (a / b) with hm | hm
    · left; exact ⟨hm, h2, h3, h4, h5, h6⟩
    · right; exact ⟨h1, hm, h3, h4, h5, h6⟩
  · rcases le_total b (((B.b0 + B.b1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, hm, h5, h6⟩
    · right; exact ⟨h1, h2, hm, h4, h5, h6⟩
  · rcases le_total E ((((B.t0 + B.t1) / 2 : ℚ) : ℝ) * ((H a + H b) / 2)) with hm | hm
    · left; exact ⟨h1, h2, h3, h4, h5, hm⟩
    · right; exact ⟨h1, h2, h3, h4, hm, h6⟩
  · left
    have e : 2 * (ax + 3) = 2 * ax + 6 := by ring
    simp only [sStep, e]
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## Route rows (verbatim copies) and the per-leaf obligation -/

/-- Strict psi-activity at the parent (verbatim copy of `CKRoute.PsiActive`). -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- Row "otherwise" of the same-side table: the complete 160,789-leaf finite cover of root (S)
(verbatim copy of `CKRoute.SS_Compact`). -/
def SSCompactRow : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.b ≤ 1 / 2 →
    1 / 16 < μ.a + μ.b → 1 / 4294967296 < μ.a / μ.b → PsiActive μ → μ.gap ≤ μ.cost

/-- Central mean square (verbatim copy of `CKRoute.CentralSquare`). -/
def CentralSquareRow : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → PsiActive μ → μ.gap ≤ μ.cost

/-- `SS_Compact`-row obligation on the physical image of an (S) box. -/
def SLeafOK (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.b ≤ 1 / 2 → 1 / 16 < μ.a + μ.b →
    1 / 4294967296 < μ.a / μ.b → InS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-! ## Root containment -/

theorem two_rpow_neg_32 : (2 : ℝ) ^ (-(32 : ℝ)) = 1 / 4294967296 := by
  rw [Real.rpow_neg (by norm_num), show (32 : ℝ) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- Every law of the `SS_Compact` row lies in the image of the root box. -/
theorem inS_sRoot {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hm : 1 / 16 < μ.a + μ.b) (hr : 1 / 4294967296 < μ.a / μ.b) :
    InS sRoot μ.a μ.b μ.meanEntropy := by
  have hbpos : 0 < μ.b := μ.b_interior.1
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  have hEle : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [sRoot]
    rw [show ((32 : ℚ) : ℝ) = (32 : ℝ) by norm_num, two_rpow_neg_32]
    exact hr.le
  · simp only [sRoot]
    rw [show ((0 : ℚ) : ℝ) = (0 : ℝ) by norm_num, neg_zero, Real.rpow_zero]
    exact (div_le_one hbpos).mpr hab
  · simp only [sRoot]; push_cast; linarith
  · simp only [sRoot]; push_cast; exact hb
  · simp only [sRoot]; push_cast; linarith
  · simp only [sRoot]; push_cast; linarith

/-! ## Adapters to `SLeafOK` -/

/-- psi-candidate Bellman statement on the image of a box. -/
def SemS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InS B μ.a μ.b μ.meanEntropy →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Owner form on the image of a box (canonical orientation, weak psi activity). -/
def OwnerS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → InS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Owner form with strictly ordered means (`a < b`, e.g. Lane M1's `SemSS`). -/
def OwnerStrictS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → InS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Row-shaped leaf statement (canonical orientation, strict psi activity; e.g. `CKLaneE.LeafS`). -/
def RowS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → InS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Parent dominance (psi not strictly active) on the image of a box. -/
def ParentS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InS B μ.a μ.b μ.meanEntropy →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

theorem sLeafOK_of_semS {B : SBox} (h : SemS B) : SLeafOK B := by
  intro k μ _ _ _ _ hin hact
  exact (hybrid_gap_le_psi hact.le).trans (h k μ hin)

theorem sLeafOK_of_ownerS {B : SBox} (h : OwnerS B) : SLeafOK B := by
  intro k μ hab _ _ _ hin hact
  exact h k μ hab hin hact.le

theorem sLeafOK_of_ownerStrictS {B : SBox} (h : OwnerStrictS B) : SLeafOK B := by
  intro k μ hab _ _ _ hin hact
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact h k μ hlt hin hact.le
  · exact μ.equal_mean_hybrid heq

theorem sLeafOK_of_rowS {B : SBox} (h : RowS B) : SLeafOK B := by
  intro k μ hab _ _ _ hin hact
  exact h k μ hab hin hact

theorem sLeafOK_of_parentS {B : SBox} (h : ParentS B) : SLeafOK B := by
  intro k μ _ _ _ _ hin hact
  exact absurd (h k μ hin) (not_le.mpr hact)

/-- A box inside `1/10 ≤ a` is owned by the central mean square row. -/
theorem sLeafOK_of_central {B : SBox} (hc : ∀ a b E : ℝ, InS B a b E → 1 / 10 ≤ a)
    (hcs : CentralSquareRow) : SLeafOK B := by
  intro k μ hab hb _ _ hin hact
  exact hcs k μ hab (by linarith) (hc _ _ _ hin) (by linarith) hact

/-- A box inside `a + b ≤ 1/16` carries the obligation vacuously. -/
theorem sLeafOK_of_smallMean {B : SBox} (hs : ∀ a b E : ℝ, InS B a b E → a + b ≤ 1 / 16) :
    SLeafOK B := by
  intro k μ _ _ hm _ hin _
  exact absurd (hs _ _ _ hin) (not_le.mpr hm)

end CKLaneG3

end


