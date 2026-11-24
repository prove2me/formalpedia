-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:03.847401+00:00
-- url     : https://prove2.me/theorems/a73a0434-8167-4303-b96f-184930ced889
-- title:
--   Iface Inh
-- statement:
--   Definitions and structural lemmas for Iface Inh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IfaceInh.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv

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
noncomputable section
instance isRegularRing_fin_zero : IsRegularRing (MvPolynomial (Fin 0) ℂ) :=
  IsRegularRing.of_ringEquiv (isEmptyRingEquiv ℂ (Fin 0)).symm
def locRingBotEquiv (p : Fin 0 → ℂ) : locPt p ≃+* locRing (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) p :=
  (RingEquiv.quotientBot (locPt p)).symm.trans (Ideal.quotEquivOfEq Ideal.map_bot.symm)
end
end ReciprocityTheory.AnForm.R


