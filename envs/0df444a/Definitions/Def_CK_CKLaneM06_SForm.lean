-- Prove2me | Definitions.Def_CK_CKLaneM06_SForm
-- name    : CK_CKLaneM06_SForm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T08:17:21.138669+00:00
-- url     : https://prove2.me/theorems/0598ba46-6a73-4821-b324-202e60cf7e75
-- title:
--   Courtade–Kumar proof module `CKLaneM06.SForm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.SForm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.SForm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.SForm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/SForm.lean)

import Definitions.Def_CK_CKLaneM06_Subtree

-- ===== source module CKLaneM06.SForm =====
section

/-!
# Lane M06: the BRIEF §7 same-side box form (`SBox` / `sBox` / `InS`)

BRIEF §7 (S): the archived box is the exact `COVER.reconstruct` from root `[[0,32],[1/32,1/2],[0,1]]`, and
`InS B a b E := 2^(-x1) ≤ a/b ≤ 2^(-x0) ∧ b0 ≤ b ≤ b1 ∧ t0*C0 ≤ E ≤ t1*C0` (real rpow,
`C0 = (H a + H b)/2`).  This module states that form field for field (lane-local copy; a one-line
adapter to Lane G's canonical `CKLaneG` definitions is added when they are published) and proves it
equivalent, for interior laws, to the coordinate-map membership `InBox` used by the checker.

* `inS_iff_inBox`   : `InS B μ.a μ.b μ.meanEntropy ↔ InBox B.toBox μ`
* `toBox_sBox`      : `(sBox p).toBox = pathBox p`
* `ParentDominance.toParentS` : parent dominance on `pathBox p` gives it on `InS (sBox p)`.
-/

set_option autoImplicit false

namespace CKLaneM06

open GeneralCK

/-- Archived same-side box with the BRIEF §7 field names: `x ∈ [x0,x1]`, `b ∈ [b0,b1]`, `t ∈ [t0,t1]`. -/
structure SBox where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving DecidableEq, Repr

/-- Root (S) `[0,32] × [1/32,1/2] × [0,1]`. -/
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

/-- The exact archived box of a path (digits). -/
def sBox (p : List ℕ) : SBox := p.foldl sStep sRoot

/-- BRIEF §7 membership: `2^(-x1) ≤ a/b ≤ 2^(-x0) ∧ b0 ≤ b ≤ b1 ∧ t0*C0 ≤ E ≤ t1*C0`. -/
def InS (B : SBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(B.x1 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x0 : ℝ)) ∧
    (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (B.t0 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t1 : ℝ) * ((H a + H b) / 2)

/-- Parent dominance on an S-box (the method conclusion of `parent_tail`). -/
def ParentS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InS B μ.a μ.b μ.meanEntropy →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

/-- Strictly psi-active owner statement on an S-box (vacuous under parent dominance). -/
def OwnerS (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InS B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem ParentS.ownerS {B : SBox} (h : ParentS B) : OwnerS B :=
  fun k μ hB hact => absurd (h k μ hB) (not_le.mpr hact)

/-- Field renaming to the checker's box type. -/
def SBox.toBox (B : SBox) : Box := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toBox_sStep (B : SBox) (d : ℕ) : (sStep B d).toBox = step B.toBox d := by
  rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl

theorem toBox_sBox (p : List ℕ) : (sBox p).toBox = pathBox p := by
  suffices h : ∀ B : SBox, (p.foldl sStep B).toBox = p.foldl step B.toBox from h sRoot
  induction p with
  | nil => intro B; rfl
  | cons d p ih =>
    intro B
    simp only [List.foldl_cons]
    rw [ih, toBox_sStep]

/-- For interior laws, the BRIEF §7 form and the coordinate-map form of box membership agree. -/
theorem inS_iff_inBox {ι : Type*} [Fintype ι] (B : SBox) (μ : InteriorLaw ι) :
    InS B μ.a μ.b μ.meanEntropy ↔ InBox B.toBox μ := by
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hab : 0 < μ.a / μ.b := div_pos ha.1 hb.1
  have hC : 0 < (H μ.a + H μ.b) / 2 := capMean_pos μ
  unfold InS InBox Box.Mem xcoord tcoord capMean SBox.toBox
  dsimp only
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, h3, h4, ?_, ?_⟩
    · have h := (Real.logb_le_iff_le_rpow (by norm_num) hab).mpr h2
      linarith
    · have h := (Real.le_logb_iff_rpow_le (by norm_num) hab).mpr h1
      linarith
    · rw [le_div_iff₀ hC]
      exact h5
    · rw [div_le_iff₀ hC]
      exact h6
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, h3, h4, ?_, ?_⟩
    · have hx : -(B.x1 : ℝ) ≤ Real.logb 2 (μ.a / μ.b) := by linarith
      exact (Real.le_logb_iff_rpow_le (by norm_num) hab).mp hx
    · have hx : Real.logb 2 (μ.a / μ.b) ≤ -(B.x0 : ℝ) := by linarith
      exact (Real.logb_le_iff_le_rpow (by norm_num) hab).mp hx
    · rwa [le_div_iff₀ hC] at h5
    · rwa [div_le_iff₀ hC] at h6

theorem ParentDominance.toParentS {p : List ℕ} (h : ParentDominance (pathBox p)) :
    ParentS (sBox p) := by
  intro k μ hS
  apply h k μ
  rw [← toBox_sBox]
  exact (inS_iff_inBox (sBox p) μ).mp hS

theorem ParentS.toParentDominance {p : List ℕ} (h : ParentS (sBox p)) :
    ParentDominance (pathBox p) := by
  intro k μ hB
  apply h k μ
  rw [← toBox_sBox] at hB
  exact (inS_iff_inBox (sBox p) μ).mpr hB

end CKLaneM06

end


