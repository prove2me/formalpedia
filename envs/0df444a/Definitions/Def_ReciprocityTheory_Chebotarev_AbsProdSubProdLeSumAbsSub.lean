-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
-- name    : ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:45.585684+00:00
-- url     : https://prove2.me/theorems/321e3d65-a7d0-403e-bb51-595fae0b85ef
-- title:
--   Abs Prod Sub Prod Le Sum Abs Sub
-- statement:
--   Definitions and structural lemmas for Abs Prod Sub Prod Le Sum Abs Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace ReciprocityTheory.Cheb
noncomputable def tent (t : ℝ) : ℝ := max 0 (1 - |t|)
section Product
variable {ι : Type*} [Fintype ι]
noncomputable def Tent (y : ι → ℝ) : ℝ := ∏ i, tent (y i)
end Product
end ReciprocityTheory.Cheb


