-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:26:58.866994+00:00
-- url     : https://prove2.me/theorems/50d1fb0e-ec57-4925-b493-2299fc1acc68
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularInverseBoxes` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularInverseBoxes` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularInverseBoxes` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularInverseBoxes (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularInverseBoxes.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularGermJet

-- ===== source module GeneralCK.Certificates.E8TAxisRegularInverseBoxes =====
section

/-! The existing four-box arithmetic interpreted through the regular jet. -/
namespace GeneralCK.Certificates.E8TAxisFirstCellBridge

open E8TAxisRegularGermJet E8TAxisMixedCoefficients

def InverseBoxes.ContainsRegularAt {p : ℕ} (b : InverseBoxes p) (s t : ℝ) : Prop :=
  b.a.Contains regularQJet t ∧ b.b.Contains regularQJet (2*s+t) ∧
    b.c.Contains regularQJet (s+t) ∧ b.d.Contains regularQJet s

theorem InverseBoxes.coeff_regular_sound {p : ℕ} {b : InverseBoxes p} {s t : ℝ}
    (h : b.ContainsRegularAt s t) (i j : ℕ) :
    (b.coeff i j).Contains (mixed regularQJet s t i j) :=
  mixedBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

#print axioms InverseBoxes.coeff_regular_sound
end GeneralCK.Certificates.E8TAxisFirstCellBridge

end


