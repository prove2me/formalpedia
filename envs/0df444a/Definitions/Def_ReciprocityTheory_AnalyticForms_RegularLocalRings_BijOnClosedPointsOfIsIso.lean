-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:06.854516+00:00
-- url     : https://prove2.me/theorems/014460c5-c8ab-4319-84c6-0d2eff2a0fcf
-- title:
--   Bij On Closed Points Of Is Iso
-- statement:
--   Definitions and structural lemmas for Bij On Closed Points Of Is Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}
end
end ReciprocityTheory.AnForm.R


