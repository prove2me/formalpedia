-- Prove2me | Definitions.Def_CK_CKLaneN1c_TransitionLiteral
-- name    : CK_CKLaneN1c_TransitionLiteral
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T23:44:40.607202+00:00
-- url     : https://prove2.me/theorems/383fd3a0-19bd-4c35-adb7-9d57c3d5b0cf
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.TransitionLiteral` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.TransitionLiteral` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.TransitionLiteral` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.TransitionLiteral (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/TransitionLiteral.lean)

import Definitions.Def_CK_CKLaneN1c_Transition
import Definitions.Def_CK_CKLaneN1c_Collar

-- ===== source module CKLaneN1c.TransitionLiteral =====
section

/-!
# Lane N1c-c: `CKLaneN1.SR_Transition` along the literal archived route

Same assembly as `CKLaneN1c.row_SR_Transition`, except that the 4 `prior_collar` leaves are routed
through the archived analytic delegate (transition `PROOF.md` §4 → `SHARPER_COLLARS.md`):

* `CKLaneG1.OppTransition.collar_region` (lane G1, the archived rule `y₁ ≤ 1 ∧ x₀ ≥ 5`,
  `y₁ ≤ 2 ∧ x₀ ≥ 6`, `y₁ ≤ 4 ∧ x₀ ≥ 8`) puts each leaf image in one of the three collars;
* the shared-entropy cap is automatic: `E ≤ 11/200 < H(1/10) ≤ min(H a, H b)` (`transition_cap`);
* `CKLaneN1c.Collar.sharper_collars` closes the psi-active branch.

`outside`, `endpoint`, `normalized_phi_children` are exactly as in `row_SR_Transition`.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- In the transition domain the collars' shared-entropy cap holds:
`E ≤ 11/200 < 37/80 ≤ H(1/10) ≤ min(H a, H b)` (transition `PROOF.md` §4; `1/10 ≤ 1 - b ≤ 1/2`
follows from `1/10 ≤ a`, `a + b ≤ 1`, `1/2 ≤ b`). -/
theorem transition_cap {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1)
    (ha : 1 / 10 ≤ μ.a) (hb : 1 / 2 ≤ μ.b) (hE : μ.meanEntropy ≤ 11 / 200) :
    μ.meanEntropy ≤ min (H μ.a) (H μ.b) := by
  have h10 := Gain.H_tenth_ge
  have hA : H (1 / 10) ≤ H μ.a := CKLaneD.H_mono_left (by norm_num) ha (by linarith)
  have hB : H (1 / 10) ≤ H μ.b := by
    rw [← H_complement μ.b]
    exact CKLaneD.H_mono_left (by norm_num) (by linarith) (by linarith)
  exact le_min (by linarith) (by linarith)

/-- Family theorem, label `prior_collar` (code 3), literal route: every archived `prior_collar` leaf
image lies in a SHARPER_COLLARS row (`collar_region`), where `sharper_collars` applies. -/
theorem collar_family_literal : ∀ q ∈ OppTransition.tree.leaves, q.2 = 3 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost := by
  intro q hq hl k μ hab hsum ha hb _hb9 _hd hE _h4 _h8 hin hact
  have hEpos := CKLaneD.law_meanEntropy_pos μ
  have hreg := OppTransition.collar_region q hq hl μ.a μ.b μ.meanEntropy hin hEpos
  exact Collar.sharper_collars k μ hab hsum (transition_cap μ hab hsum ha hb hE) hreg hact

/-- `SR_Transition` along the literal archived route (collars through SHARPER_COLLARS). -/
theorem row_SR_Transition_literal : SR_Transition := by
  intro k μ hab hsum ha hb hb9 hd hE h4 h8 hact
  obtain ⟨q, hq, hin⟩ := OppTransition.cover_law μ hsum hb hd hE h4 h8
  have hlt : q.2 < 4 := by
    have h := List.all_eq_true.mp tree_labels q hq
    simpa using h
  have hcases : q.2 = 0 ∨ q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact absurd hin (OppTransition.outside_empty q hq h0 μ.a μ.b μ.meanEntropy ha hb hd h8)
  · exact endpoint_family q hq h1 k μ hab hsum ha hb hb9 hd hE h4 h8 hin hact
  · exact normalized_family q hq h2 k μ hab hsum ha hb hb9 hd hE h4 h8 hin hact
  · exact collar_family_literal q hq h3 k μ hab hsum ha hb hb9 hd hE h4 h8 hin hact

end CKLaneN1c

end


