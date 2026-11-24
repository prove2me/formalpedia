-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
-- name    : ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:18.567004+00:00
-- url     : https://prove2.me/theorems/60119450-9d45-4239-88d2-2c7bf28598cd
-- title:
--   Constant Coeff Row Subst
-- statement:
--   Definitions and structural lemmas for Constant Coeff Row Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ConstantCoeffRowSubst.lean

import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
namespace ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
end ReciprocityTheory.PGsh


