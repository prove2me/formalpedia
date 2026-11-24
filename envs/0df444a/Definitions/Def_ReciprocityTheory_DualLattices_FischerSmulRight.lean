-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
-- name    : ReciprocityTheory_DualLattices_FischerSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:39.11975+00:00
-- url     : https://prove2.me/theorems/e004b5f4-7c5f-4aee-927d-1a3cf887c416
-- title:
--   Fischer Smul Right
-- statement:
--   Definitions and structural lemmas for Fischer Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FischerSmulRight.lean

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
namespace ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
def fw (A : Fin ν × ι →₀ ℕ) : ℂ := ((A.prod fun _ e => e.factorial : ℕ) : ℂ)
end ReciprocityTheory.PGsh


