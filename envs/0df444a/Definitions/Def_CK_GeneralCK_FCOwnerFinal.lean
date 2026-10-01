-- Prove2me | Definitions.Def_CK_GeneralCK_FCOwnerFinal
-- name    : CK_GeneralCK_FCOwnerFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:56:33.887129+00:00
-- url     : https://prove2.me/theorems/2a0573bc-7fc9-4be4-8aae-0e8524584500
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCOwnerFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCOwnerFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCOwnerFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCOwnerFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCOwnerFinal.lean)

import Definitions.Def_CK_GeneralCK_FCCapped
import Definitions.Def_CK_GeneralCK_FCOwner

-- ===== source module GeneralCK.FCOwnerFinal =====
section

/-!
# Lane F-C: the owner, modulo ONE scalar inequality

Combining `FCOwner.owner_of_capped` with `FCCapped.capped_certificate_of_scalar`,
the exact target

  `GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`

now follows from a single scalar inequality on the capped region.  No support
objects, no allocation intervals, no `childFloor` appear in the residue: it is a
statement about `eta`, `F` and `psi` alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCOwnerFinal

open GeneralCK

/-- **The lane's residue, in its sharpest compiled form.** -/
theorem owner_of_capped_scalar
    (h : ∀ a b E : ℝ, 0 < a → a < b → a + b < 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      H a ≤ E * (1 - 2 * a) / (b - a) →
      eta E - F (b - a) E ≤ F (1 - a - b) E + psi b (2 * E) / 2) :
    OppositeCornerPhiAffineCertificate.CertificateOwner := by
  apply FCOwner.owner_of_capped
  intro a b E ha hab hlt hlarge hb hcut hE hEcap hactive hcapped
  have hcut' : a + (1 - b) < 1 / 10000 := by
    rw [FCOwner.retainedCutoff_eq] at hcut
    exact hcut
  exact FCCapped.capped_certificate_of_scalar ha hab hlt hb hcut' hE hEcap hactive
    (h a b E ha hab hlt hlarge hb hcut hE hEcap hactive hcapped)

#check @owner_of_capped_scalar
#print axioms owner_of_capped_scalar

end GeneralCK.FCOwnerFinal

end


