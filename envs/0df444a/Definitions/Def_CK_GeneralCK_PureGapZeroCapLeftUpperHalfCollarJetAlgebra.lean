-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarJetAlgebra
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarJetAlgebra
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:10:53.685865+00:00
-- url     : https://prove2.me/theorems/f2a9cae1-9da5-41fa-881e-1d06872841b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarJetAlgebra` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarJetAlgebra` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarJetAlgebra` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarJetAlgebra (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarJetAlgebra.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarQuartic

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarJetAlgebra =====
section

/-!
Pure algebra for the proposed real-series degree-four jets. This file
does not prove that the actual entropy/contact functions equal these jets
up to an order-six remainder.
-/

namespace GeneralCK

noncomputable def leftUpperHalfD2 (z w L : ℝ) : ℝ :=
  (z ^ 2 + w ^ 2) / L

noncomputable def leftUpperHalfD4 (z w L : ℝ) : ℝ :=
  2 * (z ^ 4 + w ^ 4) / (3 * L)

noncomputable def leftUpperHalfInteriorJet (z w L : ℝ) : ℝ :=
  2 * (z - w) ^ 2 / L +
    8 * (z - w) * (z ^ 3 - w ^ 3) / (3 * L)

noncomputable def leftUpperHalfFJet (r D2 L : ℝ) : ℝ :=
  2 * r ^ 2 / L + 2 * r ^ 2 * D2 / L +
    (2 / (3 * L) - 1 / L ^ 2) * r ^ 4

noncomputable def leftUpperHalfEtaJet (D2 D4 L : ℝ) : ℝ :=
  4 * D2 + 4 * D4 + 4 * L * D2 ^ 2 / 3

noncomputable def leftUpperHalfEtaBJet (w L : ℝ) : ℝ :=
  4 * w ^ 2 / L + 16 * w ^ 4 / (3 * L)

noncomputable def leftUpperHalfCombinedJet (z w L : ℝ) : ℝ :=
  leftUpperHalfInteriorJet z w L +
    2 * leftUpperHalfFJet z (leftUpperHalfD2 z w L) L -
    leftUpperHalfFJet (z - w) (leftUpperHalfD2 z w L) L -
    leftUpperHalfEtaJet (leftUpperHalfD2 z w L)
      (leftUpperHalfD4 z w L) L +
    leftUpperHalfEtaBJet w L

theorem leftUpperHalfCombinedJet_eq_quartic {z lambda L : ℝ}
    (hL : L ≠ 0) :
    leftUpperHalfCombinedJet z (lambda * z) L =
      z ^ 4 * leftUpperQuarticCoefficient L lambda := by
  unfold leftUpperHalfCombinedJet leftUpperHalfInteriorJet
    leftUpperHalfFJet leftUpperHalfD2 leftUpperHalfD4
    leftUpperHalfEtaJet leftUpperHalfEtaBJet
    leftUpperQuarticCoefficient leftUpperQuarticNumerator
  field_simp [hL]
  ring

#print axioms leftUpperHalfCombinedJet_eq_quartic

end GeneralCK

end


