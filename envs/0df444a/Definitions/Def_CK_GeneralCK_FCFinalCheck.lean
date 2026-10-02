-- Prove2me | Definitions.Def_CK_GeneralCK_FCFinalCheck
-- name    : CK_GeneralCK_FCFinalCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:30:52.216997+00:00
-- url     : https://prove2.me/theorems/c075b054-970f-4bfa-884a-79e87871ceb9
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCFinalCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCFinalCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCFinalCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCFinalCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCFinalCheck.lean)

import Definitions.Def_CK_GeneralCK_FCCappedScalar

-- ===== source module GeneralCK.FCFinalCheck =====
section

/-!
# Lane F-C: exact-type closure check

`exact_target` is stated with the target's type written out by NAME, so that a
mismatch between what this lane proved and
`GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`
would be a type error rather than a prose claim.

`exact_target_unfolded` writes the SAME proposition out in full, exactly as it
appears at `GeneralCK/OppositeCornerPhiAffineCertificate.lean:28-34`, and is
inhabited by the same term.  If the definition on disk differed from the one
this lane reduced, this declaration would not elaborate.

`downstream_owner` discharges the consumer the corpus actually wants,
`FinalProductionAssemblyPositiveCutoff.OppositeCornerBelowCutoffPhiHybridOwner`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCFinalCheck

open GeneralCK

/-- The exact target, by name. -/
theorem exact_target : OppositeCornerPhiAffineCertificate.CertificateOwner :=
  FCCappedScalar.certificate_owner

/-- The exact target, written out in full. -/
theorem exact_target_unfolded :
    ∀ a b E : ℝ, 0 < a → a < b → a + b ≤ 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      ∃ (L : PsiAffineChildCertificate.EntropySupport a)
        (R : PsiAffineChildCertificate.EntropySupport b),
        OppositeCornerPhiAffineCertificate.certificateInequality L R E :=
  FCCappedScalar.certificate_owner

/-- The consumer the corpus wants. -/
theorem downstream_owner :
    FinalProductionAssemblyPositiveCutoff.OppositeCornerBelowCutoffPhiHybridOwner :=
  OppositeCornerPhiAffineCertificate.toOppositeCornerBelowCutoffPhiHybridOwner
    FCCappedScalar.certificate_owner

#check @exact_target
#check @exact_target_unfolded
#check @downstream_owner
#print axioms exact_target
#print axioms exact_target_unfolded
#print axioms downstream_owner

end GeneralCK.FCFinalCheck

end


