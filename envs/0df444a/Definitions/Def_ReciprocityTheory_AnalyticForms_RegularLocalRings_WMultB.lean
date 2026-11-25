-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultB
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:16.933236+00:00
-- url     : https://prove2.me/theorems/bf3dff62-6dcb-4fda-8465-69c77005a3f4
-- title:
--   WMult B
-- statement:
--   Definitions and structural lemmas for WMult B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory MvPolynomial
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
end ReciprocityTheory.AnForm.R.WMult


