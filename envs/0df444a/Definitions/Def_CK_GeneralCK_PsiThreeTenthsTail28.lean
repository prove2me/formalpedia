-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsTail28
-- name    : CK_GeneralCK_PsiThreeTenthsTail28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:17:12.284045+00:00
-- url     : https://prove2.me/theorems/4aa99cca-13b8-4d23-a921-bc96674c54c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsTail28` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsTail28` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsTail28` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsTail28 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsTail28.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy28
import Definitions.Def_CK_GeneralCK_PsiThreeTenthsCentralTail37

-- ===== source module GeneralCK.PsiThreeTenthsTail28 =====
section

/-!
# Exact opposite active-Psi remainders after the ratio-28 exclusion

The central chart has `q ≤ 2/5` automatically. The compact chart uses that
bias bound as an explicit clipping premise. The closed face `q = 28E` is
excluded by strict parent dominance in both charts.
-/

namespace GeneralCK.PsiThreeTenthsTail28

theorem law_active_bias_lt_twenty_eight_entropy
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 2 / 5)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 28 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  exact PsiOuterEntropy28.active_bias_lt_twenty_eight_entropy hq hE (by rwa [hm])

def centralRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsCentralTail37.centralRegion a b E ∧ 1 - a - b < 28 * E

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem toTail37CentralOwner (h : CentralOwner) :
    PsiThreeTenthsCentralTail37.CentralOwner := by
  intro k μ hab hregion hactive
  have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
    hregion.1.1.1.1.1.1.1.1.1
  have hq : 1 - μ.a - μ.b ≤ 2 / 5 := by
    linarith [hbase.2.1, hbase.2.2.1]
  exact h k μ hab ⟨hregion,
    law_active_bias_lt_twenty_eight_entropy μ hq hactive.le⟩ hactive

/-- High-bias central certificates now start strictly above entropy 3/280. -/
theorem central_high_bias_entropy_lower {a b E : ℝ}
    (hregion : centralRegion a b E) (hq : 3 / 10 < 1 - a - b) :
    3 / 280 < E := by
  linarith [hregion.2]

def compactRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsBias.compactRegion a b E ∧
    (1 - a - b ≤ 2 / 5 → 1 - a - b < 28 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- Direct conversion to the compact field of the current residual package. -/
theorem toThreeTenthsCompactOwner (h : CompactOwner) :
    PsiThreeTenthsBias.CompactOwner := by
  intro k μ hregion hactive
  apply h k μ ⟨hregion, ?_⟩ hactive
  intro hq
  exact law_active_bias_lt_twenty_eight_entropy μ hq hactive.le

#print axioms law_active_bias_lt_twenty_eight_entropy
#print axioms toTail37CentralOwner
#print axioms central_high_bias_entropy_lower
#print axioms toThreeTenthsCompactOwner

end GeneralCK.PsiThreeTenthsTail28

end


