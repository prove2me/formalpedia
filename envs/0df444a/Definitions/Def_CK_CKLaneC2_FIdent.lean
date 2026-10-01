-- Prove2me | Definitions.Def_CK_CKLaneC2_FIdent
-- name    : CK_CKLaneC2_FIdent
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:18:01.804219+00:00
-- url     : https://prove2.me/theorems/f0d309b7-7ef5-4358-8790-144aef3da1f4
-- title:
--   Courtade–Kumar proof module `CKLaneC2.FIdent` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.FIdent` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.FIdent` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.FIdent (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/FIdent.lean)

import Definitions.Def_CK_CKLaneC2_Deriv

-- ===== source module CKLaneC2.FIdent =====
section
/-
Lane C2 — the small-`c` pre-cancellation identity.

With `A = 2c + c^3 a1`, `B = c^2 + c^4 b1` (i.e. `a1 = a1f c`, `b1 = b1f c`), the nested sign
expression factors exactly as
    `Wt c = c^5 · F(c, a1, b1, L)`,   `F = Ex.evalR [c, a1, b1, L] Fex`  (185 monomials).
This is the `k = 3` cancellation carried SYMBOLICALLY: all terms of order `c^0 … c^4` vanish
identically, so `F` is evaluated with no cancellation near `c = 0`.  Pure algebra (`ring`).
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

theorem Wt_eq_F {c : ℝ} (h0 : 0 < c) :
    Wt c = c ^ 5 * Ex.evalR [c, a1f c, b1f c, Real.log 2] Fex := by
  have hc : c ≠ 0 := h0.ne'
  have hA : Af c = 2 * c + c ^ 3 * a1f c := by
    unfold a1f; field_simp; ring
  have hB : Bf c = c ^ 2 + c ^ 4 * b1f c := by
    unfold b1f; field_simp; ring
  have hK : Kf c = Real.log 2 + (c ^ 2 + c ^ 4 * b1f c) / 2 := by
    unfold Kf; rw [hB]
  have hE : Ef c = Real.log 2 + (c ^ 2 + c ^ 4 * b1f c) / 2 - c * (2 * c + c ^ 3 * a1f c) / 2 := by
    unfold Ef; rw [hA, hB]
  unfold Wt
  rw [hK, hE, hA]
  generalize a1f c = a
  generalize b1f c = b
  generalize Real.log 2 = L
  simp only [Wex, Fex, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  ring

end CKLaneC2

end


