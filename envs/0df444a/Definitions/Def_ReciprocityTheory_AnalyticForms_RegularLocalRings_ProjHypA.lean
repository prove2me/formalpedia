-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:33.573215+00:00
-- url     : https://prove2.me/theorems/a2b7245c-94b1-5e93-8c4a-4f7261cce7ac
-- title:
--   Proj Hyp A
-- statement:
--   Definitions and structural lemmas for Proj Hyp A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
end
end ReciprocityTheory.AnForm.R


