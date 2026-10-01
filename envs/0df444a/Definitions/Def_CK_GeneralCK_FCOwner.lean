-- Prove2me | Definitions.Def_CK_GeneralCK_FCOwner
-- name    : CK_GeneralCK_FCOwner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:49:35.907603+00:00
-- url     : https://prove2.me/theorems/710cea22-10a0-4a9e-a85f-1ee249e7687e
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCOwner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCOwner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCOwner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCOwner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCOwner.lean)

import Definitions.Def_CK_GeneralCK_FCRayMain

-- ===== source module GeneralCK.FCOwner =====
section

/-!
# Lane F-C: the owner, modulo the capped sub-case

`owner_of_capped` reduces
`GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`
to the single remaining sub-case in which the ray construction is out of range,
i.e. `H a ≤ E·(1-2a)/(b-a)`.  Everything else — the boundary face `a + b = 1`
(exact equality, `FCPilot.face_certificate`) and the strict interior with the ray
construction in range (`FCRayMain.ray_certificate`) — is already closed.

Nothing here is renamed, weakened or generalised: the conclusion is the exact
target type and the hypothesis is a strictly smaller region of the same domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCOwner

open GeneralCK
open GeneralCK.PsiAffineChildCertificate

theorem retainedCutoff_eq : SmallMeanPhiCutoff.retainedCutoff = (1 / 10000 : ℝ) := rfl

/-- **Exact reduction.**  The owner follows from the capped sub-case alone. -/
theorem owner_of_capped
    (h : ∀ a b E : ℝ, 0 < a → a < b → a + b < 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      H a ≤ E * (1 - 2 * a) / (b - a) →
      ∃ (L : EntropySupport a) (R : EntropySupport b),
        OppositeCornerPhiAffineCertificate.certificateInequality L R E) :
    OppositeCornerPhiAffineCertificate.CertificateOwner := by
  apply FCPilot.owner_of_strict_interior
  intro a b E ha hab hlt hlarge hb hcut hE hEcap hactive
  have hcut' : a + (1 - b) < 1 / 10000 := by
    rw [retainedCutoff_eq] at hcut
    exact hcut
  by_cases hray : E * (1 - 2 * a) / (b - a) < H a
  · exact FCRayMain.ray_certificate ha hab hlt hb hcut' hE hEcap hactive hray
  · push_neg at hray
    exact h a b E ha hab hlt hlarge hb hcut hE hEcap hactive hray

#check @owner_of_capped
#print axioms owner_of_capped

end GeneralCK.FCOwner

end


