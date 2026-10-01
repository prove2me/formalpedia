-- Prove2me | Definitions.Def_CK_CKLaneM06_Semantics
-- name    : CK_CKLaneM06_Semantics
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:58:42.198537+00:00
-- url     : https://prove2.me/theorems/74e30c48-6dd5-4b4a-b505-d76d973a791d
-- title:
--   Courtade–Kumar proof module `CKLaneM06.Semantics` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.Semantics` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.Semantics` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.Semantics (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/Semantics.lean)

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_CK_GeneralCK_PsiParentPhiFloor
import Definitions.Def_CK_GeneralCK_PsiLowEntropyLeafReplay

-- ===== source module CKLaneM06.Semantics =====
section

/-!
# Lane M06: semantics of archived same-side leaves (method `parent_tail`)

The archived same-side cover (`CK_GENERAL_COMPLETION/same_side/COVER.py`, final run
`ADAPT_RESULT.json`) lives in coordinates `(x, b, t) ∈ [0,32] × [1/32,1/2] × [0,1]` with

* `x = -log₂ (a / b)` (so `a = b·2^-x`),
* `b` the right mean,
* `t = E / C`, where `E = (e+f)/2` is the mean entropy and `C = (H a + H b)/2` the mean cap.

A leaf is identified by its path (digits `0..5`: axis = digit / 2, side = digit % 2, exact halving;
`COVER.reconstruct`).  `pathBox` recomputes the exact rational leaf box from the path.

`InBox B μ` is membership of the law `μ` in the exact box `B` through the coordinate map
`coords μ = (xcoord μ, μ.b, tcoord μ)`; its shape is identical to `CKLaneG.Box.Mem`
(`lo0 ≤ x ≤ hi0 ∧ lo1 ≤ y ≤ hi1 ∧ lo2 ≤ z ≤ hi2`).  Only the mean entropy `E` enters; the
individual child entropies `e, f` are unrestricted beyond the law itself.

The method conclusion (parent comparison) is `ParentDominance B`: `psi ≤ phi` at the parent
for every law in the box; `PsiOwnerOn B` is the resulting psi-branch owner statement
(`phi < psi → gap ≤ cost`, vacuous on the box).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06

open GeneralCK

/-- A closed rational box in archived same-side coordinates `(x, b, t)`
(axes `0, 1, 2`; same field order as `CKLaneG.Box`). -/
structure Box where
  lo0 : ℚ
  hi0 : ℚ
  lo1 : ℚ
  hi1 : ℚ
  lo2 : ℚ
  hi2 : ℚ
  deriving DecidableEq, Repr

/-- The archived same-side root `[0,32] × [1/32,1/2] × [0,1]` (`ADAPT_RESULT.json`, `root`). -/
def root : Box := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step for the archived path digit `d = 2 * axis + side`. -/
def step (B : Box) (d : ℕ) : Box :=
  match d with
  | 0 => { B with hi0 := (B.lo0 + B.hi0) / 2 }
  | 1 => { B with lo0 := (B.lo0 + B.hi0) / 2 }
  | 2 => { B with hi1 := (B.lo1 + B.hi1) / 2 }
  | 3 => { B with lo1 := (B.lo1 + B.hi1) / 2 }
  | 4 => { B with hi2 := (B.lo2 + B.hi2) / 2 }
  | 5 => { B with lo2 := (B.lo2 + B.hi2) / 2 }
  | _ => B

/-- The exact leaf box of an archived path (digits as natural numbers). -/
def pathBox (p : List ℕ) : Box := p.foldl step root

/-- Real point membership in a box (same shape as `CKLaneG.Box.Mem`). -/
def Box.Mem (B : Box) (x y z : ℝ) : Prop :=
  (B.lo0 : ℝ) ≤ x ∧ x ≤ (B.hi0 : ℝ) ∧ (B.lo1 : ℝ) ≤ y ∧ y ≤ (B.hi1 : ℝ) ∧
    (B.lo2 : ℝ) ≤ z ∧ z ≤ (B.hi2 : ℝ)

section Coords

variable {ι : Type*} [Fintype ι]

/-- Mean endpoint cap `C = (H a + H b) / 2`. -/
noncomputable def capMean (μ : InteriorLaw ι) : ℝ := (H μ.a + H μ.b) / 2

/-- Archived same-side coordinate `x = -log₂ (a / b)`. -/
noncomputable def xcoord (μ : InteriorLaw ι) : ℝ := -Real.logb 2 (μ.a / μ.b)

/-- Archived same-side coordinate `t = E / C`. -/
noncomputable def tcoord (μ : InteriorLaw ι) : ℝ := μ.meanEntropy / capMean μ

/-- The archived coordinate map `μ ↦ (x, b, t)`. -/
noncomputable def coords (μ : InteriorLaw ι) : ℝ × ℝ × ℝ := (xcoord μ, μ.b, tcoord μ)

/-- Membership of the law `μ` in the exact archived box `B`. -/
def InBox (B : Box) (μ : InteriorLaw ι) : Prop :=
  B.Mem (xcoord μ) μ.b (tcoord μ)

theorem inBox_iff_coords (B : Box) (μ : InteriorLaw ι) :
    InBox B μ ↔ B.Mem (coords μ).1 (coords μ).2.1 (coords μ).2.2 := Iff.rfl

theorem capMean_pos (μ : InteriorLaw ι) : 0 < capMean μ := by
  have ha := μ.a_interior
  have hb := μ.b_interior
  have h1 := H_pos ha.1 ha.2
  have h2 := H_pos hb.1 hb.2
  unfold capMean
  linarith

/-- Multiplicative (division- and logarithm-free) consequences of box membership. -/
theorem InBox.bounds {B : Box} {μ : InteriorLaw ι} (hB : InBox B μ) :
    (2 : ℝ) ^ (-(B.hi0 : ℝ)) * μ.b ≤ μ.a ∧ μ.a ≤ (2 : ℝ) ^ (-(B.lo0 : ℝ)) * μ.b ∧
      (B.lo1 : ℝ) ≤ μ.b ∧ μ.b ≤ (B.hi1 : ℝ) ∧
      (B.lo2 : ℝ) * capMean μ ≤ μ.meanEntropy ∧ μ.meanEntropy ≤ (B.hi2 : ℝ) * capMean μ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hab : 0 < μ.a / μ.b := div_pos ha.1 hb.1
  have hC := capMean_pos μ
  unfold xcoord at h1 h2
  unfold tcoord at h5 h6
  refine ⟨?_, ?_, h3, h4, ?_, ?_⟩
  · have hx : -(B.hi0 : ℝ) ≤ Real.logb 2 (μ.a / μ.b) := by linarith
    have h := (Real.le_logb_iff_rpow_le (by norm_num) hab).mp hx
    rwa [le_div_iff₀ hb.1] at h
  · have hx : Real.logb 2 (μ.a / μ.b) ≤ -(B.lo0 : ℝ) := by linarith
    have h := (Real.logb_le_iff_le_rpow (by norm_num) hab).mp hx
    rwa [div_le_iff₀ hb.1] at h
  · rwa [le_div_iff₀ hC] at h5
  · rwa [div_le_iff₀ hC] at h6

end Coords

/-- Method conclusion of `parent_tail` (parent comparison): on every law of the exact box, the
`phi` branch dominates the `psi` branch at the parent. -/
def ParentDominance (B : Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InBox B μ →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

/-- The psi-branch owner statement on the exact box (the canonical-branch form of
`GeneralCK.finiteHybridBellman_of_canonical_branches`, restricted to the box). -/
def PsiOwnerOn (B : Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InBox B μ →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem ParentDominance.psiOwnerOn {B : Box} (h : ParentDominance B) : PsiOwnerOn B :=
  fun k μ hB hact => absurd (h k μ hB) (not_le.mpr hact)

end CKLaneM06

end


