-- Prove2me | Definitions.Def_CK_CKLaneE_SRect
-- name    : CK_CKLaneE_SRect
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:33:11.296981+00:00
-- url     : https://prove2.me/theorems/7a1ade9f-4689-43d4-8830-5a1c7aa35a38
-- title:
--   Courtade–Kumar proof module `CKLaneE.SRect` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.SRect` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.SRect` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.SRect (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/SRect.lean)

import Definitions.Def_CK_CKLaneE_SLeaf3

-- ===== source module CKLaneE.SRect =====
section

/-!
# Lane E: shared rectangle certificates for archived (S) leaves

Archived leaves with the same `(x, b)` rectangle differ only in their `t`-slab.  The log-sum
certificates cover every entropy above the floor `t0·C0`, so one kernel-checked certificate at the
smallest `t0` of a rectangle (`RectOK X t0`) yields `LeafS` for every archived leaf of that rectangle
whose `t0` is at least that floor (`leafS_of_rect`, a cheap field comparison).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.S

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart

/-- An archived `(x, b)` rectangle. -/
structure SRect where
  x0 : ℚ
  x1 : ℚ
  b0 : ℚ
  b1 : ℚ
  deriving Repr, DecidableEq

/-- Rectangle statement with relative entropy floor `t0·C0` (no upper entropy bound). -/
def RectOK (X : SRect) (t0 : ℚ) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b →
    (2 : ℝ) ^ (-(X.x1 : ℝ)) ≤ μ.a / μ.b → μ.a / μ.b ≤ (2 : ℝ) ^ (-(X.x0 : ℝ)) →
    (X.b0 : ℝ) ≤ μ.b → μ.b ≤ (X.b1 : ℝ) →
    (t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

def rectCheck (X : SRect) (t0 r1 r2 : ℚ) (t : RT3) : Bool :=
  decide (0 ≤ X.x0 ∧ X.x0 ≤ X.x1 ∧ 0 ≤ t0 ∧ 0 < r1 ∧ r1 ≤ r2 ∧ r2 ≤ 1) &&
    (decide (X.x1 = 0) || (ptOk r1 && decide (lHi r1 ≤ -X.x1 * LqHi))) &&
    (decide (X.x0 = 0 ∧ r2 = 1) || (ptOk r2 && decide (-X.x0 * LqLo ≤ lLo r2))) &&
    t.check t0 ⟨r1, r2, X.b0, X.b1⟩

theorem rectOK_of_check (X : SRect) (t0 r1 r2 : ℚ) (t : RT3) (h : rectCheck X t0 r1 r2 t = true) :
    RectOK X t0 := by
  simp only [rectCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hx0, hxx, ht0, hr1p, hr12, hr2⟩, hA⟩, hB⟩, ht⟩ := h
  have hG := RT3.sound t0 ht0 t _ ht
  intro k μ hab hx1 hx0' hb0 hb1 hE0 hact
  rcases lt_or_eq_of_le hab with hlt | heq
  · refine hG k μ hlt ?_ ?_ hb0 hb1 hE0 hact.le
    · exact (r1_le_rpow (hx0.trans hxx) hr1p (hr12.trans hr2) hA).trans hx1
    · exact hx0'.trans (rpow_le_r2 hx0 hB)
  · exact gap_le_cost_of_eq μ heq hact.le

/-- An archived box fits a certified rectangle: same `(x, b)` rectangle, floor not above its `t0`. -/
def fits (B : SBox) (X : SRect) (t0 : ℚ) : Bool :=
  decide (B.x0 = X.x0 ∧ B.x1 = X.x1 ∧ B.b0 = X.b0 ∧ B.b1 = X.b1 ∧ t0 ≤ B.t0)

theorem leafS_of_rect (B : SBox) {X : SRect} {t0 : ℚ} (hR : RectOK X t0) (hf : fits B X t0 = true) :
    LeafS B := by
  simp only [fits, decide_eq_true_eq] at hf
  obtain ⟨e0, e1, e2, e3, ht⟩ := hf
  intro k μ hab hin hact
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hin
  rw [e1] at h1
  rw [e0] at h2
  rw [e2] at h3
  rw [e3] at h4
  have hC : 0 ≤ (H μ.a + H μ.b) / 2 := by
    have := H_nonneg μ.a_interior.1.le μ.a_interior.2.le
    have := H_nonneg μ.b_interior.1.le μ.b_interior.2.le
    linarith
  have htR : (t0 : ℝ) ≤ B.t0 := by exact_mod_cast ht
  have hE : (t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy :=
    (mul_le_mul_of_nonneg_right htR hC).trans h5
  exact hR k μ hab h1 h2 h3 h4 hE hact

end CKLaneE.S

#print axioms CKLaneE.S.leafS_of_rect
#print axioms CKLaneE.S.rectOK_of_check

end


