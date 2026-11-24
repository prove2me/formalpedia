-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
-- name    : ReciprocityTheory_Chebotarev_SplitDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:32.530813+00:00
-- url     : https://prove2.me/theorems/e744351f-e3cf-41f1-890d-5aa4653b18ea
-- title:
--   Split Def
-- statement:
--   Definitions and structural lemmas for Split Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitDef.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
namespace ReciprocityTheory.Cheb
noncomputable def under {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : Prm E where
  asIdeal := P.asIdeal.under (𝓞 E)
  isPrime := Ideal.IsPrime.under _ _
  ne_bot := Ideal.under_ne_bot (𝓞 E) P.ne_bot
end ReciprocityTheory.Cheb


