-- Prove2me | Definitions.Def_CK_GeneralCK_OppositeCornerPhiAffineCertificate
-- name    : CK_GeneralCK_OppositeCornerPhiAffineCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:26:59.821956+00:00
-- url     : https://prove2.me/theorems/92b4a562-5216-4f46-92ed-2be596e81a2d
-- title:
--   Courtade–Kumar proof module `GeneralCK.OppositeCornerPhiAffineCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.OppositeCornerPhiAffineCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.OppositeCornerPhiAffineCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.OppositeCornerPhiAffineCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/OppositeCornerPhiAffineCertificate.lean)

import Definitions.Def_CK_GeneralCK_FinalProductionAssemblyPositiveCutoff
import Definitions.Def_CK_GeneralCK_PsiAffineChildCertificate

-- ===== source module GeneralCK.OppositeCornerPhiAffineCertificate =====
section

/-!
# Three-variable certificate for the positive-cutoff opposite corner

The remaining opposite-corner owner quantifies over arbitrary finite laws.
Convex entropy supports eliminate the individual child entropies, and the
existing radial/log-sum maximum eliminates the law itself.  The resulting
certificate has only the two child means and their mean entropy as variables.
-/

namespace GeneralCK.OppositeCornerPhiAffineCertificate

open GeneralCK
open PsiAffineChildCertificate
open SmallMeanPhiCutoff

/-- Scalar comparison after choosing one sound affine lower support for each
child profile. -/
def certificateInequality {a b : ℝ} (L : EntropySupport a)
    (R : EntropySupport b) (E : ℝ) : Prop :=
  phi ((a + b) / 2) E - childFloor L R E ≤ scalarCostFloor a b E

/-- A three-real-variable owner for precisely the missing active-phi
opposite-corner region.  The support proofs are analytic objects; only the
displayed scalar comparison is intended for interval certification. -/
def CertificateOwner : Prop :=
  ∀ a b E : ℝ, 0 < a → a < b → a + b ≤ 1 → 1 / 16 < a + b →
    1 / 2 < b → a + (1 - b) < retainedCutoff →
    0 < E → E ≤ (H a + H b) / 2 →
    psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
    ∃ (L : EntropySupport a) (R : EntropySupport b),
      certificateInequality L R E

/-- The three-variable affine-support certificate implies the actual-law
hybrid owner. -/
theorem toOppositeCornerBelowCutoffPhiHybridOwner
    (h : CertificateOwner) :
    FinalProductionAssemblyPositiveCutoff.OppositeCornerBelowCutoffPhiHybridOwner := by
  intro k μ hab hsum hlarge hb hcut hactive
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hEcap : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap]
  obtain ⟨L, R, hcert⟩ := h μ.a μ.b μ.meanEntropy μ.a_interior.1 hab hsum
    hlarge hb hcut hEpos hEcap (by
      simpa only [InteriorLaw.midpoint] using hactive)
  have hchild := childFloor_lower L R μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap rfl
  have hparent : B μ.midpoint μ.meanEntropy = phi μ.midpoint μ.meanEntropy :=
    max_eq_left hactive
  have hgap : μ.gap ≤ phi μ.midpoint μ.meanEntropy - childFloor L R μ.meanEntropy := by
    unfold InteriorLaw.gap
    change B μ.midpoint μ.meanEntropy - (B μ.a μ.e + B μ.b μ.f) / 2 ≤ _
    change childFloor L R μ.meanEntropy ≤ (B μ.a μ.e + B μ.b μ.f) / 2 at hchild
    rw [hparent]
    linarith only [hchild]
  have hcert' :
      phi μ.midpoint μ.meanEntropy - childFloor L R μ.meanEntropy ≤
        scalarCostFloor μ.a μ.b μ.meanEntropy := by
    simpa only [certificateInequality, InteriorLaw.midpoint] using hcert
  exact (hgap.trans hcert').trans (scalarCostFloor_le_cost μ hab)

#print axioms toOppositeCornerBelowCutoffPhiHybridOwner

end GeneralCK.OppositeCornerPhiAffineCertificate

end


