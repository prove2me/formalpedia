-- Prove2me | Definitions.Def_CK_CKLaneN4_CentralSubrows
-- name    : CK_CKLaneN4_CentralSubrows
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:03:58.344984+00:00
-- url     : https://prove2.me/theorems/2a29589f-bcb6-4299-b0ca-77e43348c970
-- title:
--   Courtade–Kumar proof module `CKLaneN4.CentralSubrows` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.CentralSubrows` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.CentralSubrows` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.CentralSubrows (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/CentralSubrows.lean)

import Definitions.Def_CK_CKLaneN4_LowEntropy25

-- ===== source module CKLaneN4.CentralSubrows =====
section

/-!
# Lane N4: the N4-owned sub-rows of the central mean square (Lane N1 `SUBROWS.lean`)

Verbatim copies of `CKLaneN1.SR_Parent8`, `CKLaneN1.SR_Parent8Dominance`, `CKLaneN1.SR_EightRatio`,
`CKLaneN1.SR_LargeRatio` (`~/ck_lanes_20260923/N1/SUBROWS.lean`), stated with the verbatim local
`PsiActive` (`CKLaneN4.PsiActive` = `CKRoute.PsiActive` = `CKLaneN1.PsiActive`), so they bind by
`Iff.rfl`.

* `sr_parent8Dominance` / `sr_parent8`: PARENT8 (`parent8`); central opposite means give
  `q = 1 - a - b ≤ 2/5` and `q ≥ 8E > 0`.
* `sr_eightRatio`: eight-ratio theorem (3).  Proved by the global cap-free eight-ratio theorem of
  CK_GENERAL_COMPLETION (`globalEightPsi_law`), whose hypotheses (`E ≤ 11/200`, `d ≥ 8E`, `q ≤ 8E`, no
  mean restriction) contain those of the central theorem.
* `sr_largeRatio`: union of the two.
-/

namespace CKLaneN4

open GeneralCK

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≥ 8E, q ≥ 8E`: parent dominance (2); vacuous in-row. -/
def SR_Parent8 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Law-level parent-dominance form of the `SR_Parent8` domain (psi not strictly active). -/
def SR_Parent8Dominance : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≥ 8E, q ≤ 8E`: eight-ratio theorem (3). -/
def SR_EightRatio : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Union of the last two §4 rows (`d ≥ 1/50, E ≤ 11/200, d ≥ 8E`): parent8 ∪ eight-ratio. -/
def SR_LargeRatio : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a →
    PsiActive μ → μ.gap ≤ μ.cost

theorem sr_parent8Dominance : SR_Parent8Dominance := by
  intro k μ _hab hsum ha _hb _hb9 _hd50 _hEi _hd8 hq8
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  have h := parent8 (1 - μ.a - μ.b) μ.meanEntropy hE (by linarith) (by linarith) hq8
  rw [hmid] at h
  exact h.le

theorem sr_parent8 : SR_Parent8 := by
  intro k μ hab hsum ha hb hb9 hd50 hEi hd8 hq8 hact
  exact absurd (sr_parent8Dominance k μ hab hsum ha hb hb9 hd50 hEi hd8 hq8) (not_le.mpr hact)

theorem sr_eightRatio : SR_EightRatio := by
  intro k μ _hab hsum _ha _hb _hb9 _hd50 hEi hd8 hq8 hact
  exact globalEightPsi_law μ hsum hEi hd8 hq8 hact.le

theorem sr_largeRatio : SR_LargeRatio := by
  intro k μ hab hsum ha hb hb9 hd50 hEi hd8 hact
  by_cases hq8 : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b
  · exact sr_parent8 k μ hab hsum ha hb hb9 hd50 hEi hd8 hq8 hact
  · exact sr_eightRatio k μ hab hsum ha hb hb9 hd50 hEi hd8 (lt_of_not_ge hq8).le hact

end CKLaneN4

end


