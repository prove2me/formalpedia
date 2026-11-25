-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemBasicOpenSecHomIff
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_MemBasicOpenSecHomIff
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:25.844988+00:00
-- url     : https://prove2.me/theorems/ab96f8f2-e6ec-4105-b533-04d01e6c3a91
-- title:
--   Mem Basic Open Sec Hom Iff
-- statement:
--   Definitions and structural lemmas for Mem Basic Open Sec Hom Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemBasicOpenSecHomIff.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
namespace AffPres
variable (P : AffPres s)
end AffPres
end
end ReciprocityTheory.AnForm.R


