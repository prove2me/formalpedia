-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:39.589173+00:00
-- url     : https://prove2.me/theorems/8d755b7f-b6c4-4379-ac21-87cccb3e84ea
-- title:
--   Base Change C
-- statement:
--   Definitions and structural lemmas for Base Change C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeC.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]
noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭
end ReciprocityTheory.AnForm.R


