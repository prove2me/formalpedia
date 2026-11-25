-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:31.643803+00:00
-- url     : https://prove2.me/theorems/79e8f23c-f41d-434a-b974-185e8320ca43
-- title:
--   Cone Chart B
-- statement:
--   Definitions and structural lemmas for Cone Chart B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
def jacSpanAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Submodule ℂ (σ → ℂ) :=
  Submodule.span ℂ ((fun h : MvPolynomial σ ℂ => fun j => eval z (pderiv j h)) '' (I : Set _))
end ReciprocityTheory.AnForm.R


