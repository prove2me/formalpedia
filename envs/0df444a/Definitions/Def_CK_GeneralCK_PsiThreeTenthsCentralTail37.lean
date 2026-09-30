-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsCentralTail37
-- name    : CK_GeneralCK_PsiThreeTenthsCentralTail37
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:59.839509+00:00
-- url     : https://prove2.me/theorems/5b0351b2-76ce-4a50-9369-7599ba09ee2c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsCentralTail37` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsCentralTail37` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsCentralTail37` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsCentralTail37 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsCentralTail37.lean)

import Definitions.Def_CK_GeneralCK_PsiThreeTenthsCentralTail40
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy37

-- ===== source module GeneralCK.PsiThreeTenthsCentralTail37 =====
section

/-! The checked parent exclusion at `37E≤q≤2/5` narrows the opposite
central active-Psi owner. -/

namespace GeneralCK.PsiThreeTenthsCentralTail37

def centralRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsBias.centralRegion a b E ∧
    (3 / 10 < 1 - a - b → 1 - a - b < 37 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem toTail40CentralOwner (h : CentralOwner) :
    PsiThreeTenthsCentralTail40.CentralOwner := by
  intro k μ hab hregion hactive
  apply h k μ hab ⟨hregion.1, ?_⟩ hactive
  intro hq3
  have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
    hregion.1.1.1.1.1.1.1.1.1
  have hb : (1 / 2 : ℝ) ≤ μ.b := hbase.2.1
  have ha : (1 / 10 : ℝ) ≤ μ.a := hbase.2.2.1
  have hqu : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have hq0 : 0 < 1 - μ.a - μ.b := by linarith
  have htail := PsiOuterEntropy37.parent_dominance_two_fifths37
    hq0 hqu hE (le_of_not_gt hn)
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [hmid] at htail
  exact (not_lt_of_ge hactive.le) htail

#print axioms toTail40CentralOwner

end GeneralCK.PsiThreeTenthsCentralTail37

end


