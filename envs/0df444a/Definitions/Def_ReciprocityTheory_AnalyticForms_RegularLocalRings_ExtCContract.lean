-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:38.936528+00:00
-- url     : https://prove2.me/theorems/a8f282fa-fd2d-4ba1-b3aa-04cb5d583433
-- title:
--   Ext CContract
-- statement:
--   Definitions and structural lemmas for Ext CContract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExtCContract.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
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
noncomputable def projQ (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) : MvPolynomial σ ℚ :=
  ∑ m ∈ q.support, monomial m (ℓ (coeff m q))
end ReciprocityTheory.AnForm.R


