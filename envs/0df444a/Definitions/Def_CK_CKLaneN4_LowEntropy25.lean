-- Prove2me | Definitions.Def_CK_CKLaneN4_LowEntropy25
-- name    : CK_CKLaneN4_LowEntropy25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:40:14.453639+00:00
-- url     : https://prove2.me/theorems/da23c7e1-3b8d-4f86-9c39-4db8c3f1307b
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LowEntropy25` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LowEntropy25` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LowEntropy25` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LowEntropy25 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LowEntropy25.lean)

import Definitions.Def_CK_CKLaneN4_GlobalEight
import Definitions.Def_CK_CKLaneN4_ParentTheorems

-- ===== source module CKLaneN4.LowEntropy25 =====
section

/-!
# Lane N4: the outer opposite-side low-entropy corollary (`OP_LowEntropy25`)

Archive: CK_GENERAL_COMPLETION `reduction/eight_global/OUTER_OPPOSITE_LOW_ENTROPY.md`:
every positive feasible opposite-side tuple with a mean outside `[1/10, 9/10]` and `E ≤ 1/25`
satisfies `ζ ≥ R_max`.  Canonical form (`a ≤ b`, `a + b ≤ 1`, `b ≥ 1/2`, `a < 1/10`) with strict
psi-activity, as the route's rows.

Proof exactly as archived.  `q = 1 - a - b ∈ [0, 1/2)`, `d = b - a ≥ 2/5 > 8/25 ≥ 8E`.
* `q = 0`: exact parent equality `phi(1/2, E) = psi(1/2, E)` (no strict activity);
* `0 < q ≤ 2/5`, `q ≥ 8E`: PARENT8 (`parent8`) — no strict activity;
* `0 < q ≤ 2/5`, `q ≤ 8E`: global cap-free eight-ratio theorem (`globalEightPsi_law`, `E ≤ 11/200`);
* `2/5 ≤ q ≤ 1/2`, `E ≤ 1/40`: `q/E ≥ 16`, PARENT16 (`parent16`) — no strict activity;
* `2/5 ≤ q ≤ 1/2`, `1/40 ≤ E ≤ 1/25`: HIGH_Q_PARENT (`highQParent`) — no strict activity.
-/

namespace CKLaneN4

open GeneralCK

/-- Strict psi-activity at the parent (verbatim copy of `CKRoute.PsiActive`). -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- The outer opposite-side low-entropy corollary through `E = 1/25`, canonical form. -/
def OP_LowEntropy25 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a < 1 / 10 → μ.meanEntropy ≤ 1 / 25 →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Exact parent equality on the `q = 0` face. -/
theorem phi_eq_psi_half (E : ℝ) : phi (1 / 2) E = psi (1 / 2) E := by
  unfold phi psi
  norm_num [F, H_half]

theorem opLowEntropy25 : OP_LowEntropy25 := by
  intro k μ hab hsum hb ha hE25 hact
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  have hact' : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy <
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmid]
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hd8 : 8 * μ.meanEntropy ≤ μ.b - μ.a := by linarith
  rcases hq0.eq_or_lt with hz | hqpos
  · exfalso
    have h2 : (1 - (1 - μ.a - μ.b)) / 2 = 1 / 2 := by rw [← hz]; norm_num
    rw [h2, phi_eq_psi_half] at hact'
    exact lt_irrefl _ hact'
  by_cases hq25 : 1 - μ.a - μ.b ≤ 2 / 5
  · by_cases h8 : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b
    · exact absurd (parent8 _ _ hE hqpos hq25 h8) (not_lt.mpr hact'.le)
    · exact globalEightPsi_law μ hsum (by linarith) hd8 (lt_of_not_ge h8).le hact.le
  · by_cases hE40 : μ.meanEntropy ≤ 1 / 40
    · exact absurd (parent16 _ _ hE hqpos (by linarith) (by linarith)) (not_lt.mpr hact'.le)
    · exact absurd (highQParent _ _ (by linarith) (by linarith) (by linarith) hE25)
        (not_lt.mpr hact'.le)

/-- The same statement with the local `PsiActive` predicate (route form). -/
theorem opLowEntropy25' : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 2 ≤ μ.b → μ.a < 1 / 10 → μ.meanEntropy ≤ 1 / 25 → PsiActive μ → μ.gap ≤ μ.cost :=
  opLowEntropy25

end CKLaneN4

end


