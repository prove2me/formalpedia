-- Prove2me | Definitions.Def_CK_CKLaneE_SLeaf3
-- name    : CK_CKLaneE_SLeaf3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:29:16.09895+00:00
-- url     : https://prove2.me/theorems/774d542a-d33d-45e5-a8d7-f691e22c65e4
-- title:
--   Courtade–Kumar proof module `CKLaneE.SLeaf3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.SLeaf3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.SLeaf3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.SLeaf3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/SLeaf3.lean)

import Definitions.Def_CK_CKLaneE_SLeaf2
import Definitions.Def_CK_CKLaneE_CertLSK

-- ===== source module CKLaneE.SLeaf3 =====
section

/-!
# Lane E: archived-leaf refinement trees with enhanced-floor leaves (`RT3`)

`RT3` = `RT2` plus leaves certified by `CKLaneE.LSK` (relative entropy floor `t0·C0` and the
enhanced log-sum coefficient `1/(b(1-a)(2-a))` of `CKLaneE.KF.cost_floor_sameSide`).
`leafS_of_check3` is the archived-leaf bridge (conclusion `CKLaneE.S.LeafS`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.S

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart

inductive RT3
  | box (c : RC) (E1 : ℚ)
  | rel (v0S v0I v1S v1I : ℚ)
  | relk (v0S v0I v1S v1I : ℚ)
  | node (ax : ℕ) (v : ℚ) (l r : RT3)

def RT3.check (t0 : ℚ) : RT3 → Box2 → Bool
  | .box c E1, R => (RT.leaf c E1).check t0 R
  | .rel a b c d, R => LSR.check ⟨R.r1, R.r2, R.b1, R.b2, 1, 1⟩ t0 a b c d
  | .relk a b c d, R => LSK.check ⟨R.r1, R.r2, R.b1, R.b2, 1, 1⟩ t0 a b c d
  | .node ax v l r, R => l.check t0 (R.lower ax v) && r.check t0 (R.upper ax v)

theorem RT3.sound (t0 : ℚ) (ht0 : 0 ≤ t0) : ∀ (t : RT3) (R : Box2), t.check t0 R = true → GoodR t0 R
  | .box c E1, R, h => leaf_goodR t0 ht0 c E1 R h
  | .rel a b c d, R, h => by
      intro k μ hab h1 h2 h3 h4 hE hact
      exact LSR.check_sound ⟨R.r1, R.r2, R.b1, R.b2, 1, 1⟩ t0 a b c d h k μ hab h1 h2 h3 h4 hE hact
  | .relk a b c d, R, h => by
      intro k μ hab h1 h2 h3 h4 hE hact
      exact LSK.check_sound ⟨R.r1, R.r2, R.b1, R.b2, 1, 1⟩ t0 a b c d h k μ hab h1 h2 h3 h4 hE hact
  | .node ax v l r, R, h => by
      simp only [RT3.check, Bool.and_eq_true] at h
      have hl := RT3.sound t0 ht0 l _ h.1
      have hr := RT3.sound t0 ht0 r _ h.2
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

def leafCheck3 (B : SBox) (r1 r2 : ℚ) (t : RT3) : Bool :=
  decide (0 ≤ B.x0 ∧ B.x0 ≤ B.x1 ∧ 0 ≤ B.t0 ∧ 0 < r1 ∧ r1 ≤ r2 ∧ r2 ≤ 1) &&
    (decide (B.x1 = 0) || (ptOk r1 && decide (lHi r1 ≤ -B.x1 * LqHi))) &&
    (decide (B.x0 = 0 ∧ r2 = 1) || (ptOk r2 && decide (-B.x0 * LqLo ≤ lLo r2))) &&
    t.check B.t0 ⟨r1, r2, B.b0, B.b1⟩

theorem leafS_of_check3 (B : SBox) (r1 r2 : ℚ) (t : RT3) (h : leafCheck3 B r1 r2 t = true) :
    LeafS B := by
  simp only [leafCheck3, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hx0, hxx, ht0, hr1p, hr12, hr2⟩, hA⟩, hB⟩, ht⟩ := h
  have hG := RT3.sound B.t0 ht0 t _ ht
  intro k μ hab hin hact
  obtain ⟨hx1, hx0', hb0, hb1, hE0, _⟩ := hin
  rcases lt_or_eq_of_le hab with hlt | heq
  · refine hG k μ hlt ?_ ?_ hb0 hb1 hE0 hact.le
    · exact (r1_le_rpow (hx0.trans hxx) hr1p (hr12.trans hr2) hA).trans hx1
    · exact hx0'.trans (rpow_le_r2 hx0 hB)
  · exact gap_le_cost_of_eq μ heq hact.le

end CKLaneE.S

#check @CKLaneE.S.leafS_of_check3
#print axioms CKLaneE.S.leafS_of_check3

end


