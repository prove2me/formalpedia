-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
-- name    : Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:56.221404+00:00
-- url     : https://prove2.me/theorems/880e8fe5-6500-4334-953f-2530c8360143
-- title:
--   Sqrt Abs Norm Le Prod
-- statement:
--   Definitions and structural lemmas for Sqrt Abs Norm Le Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/SqrtAbsNormLeProd.lean

import Definitions.Def_Formalism_LatticeRigidity_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
end Formalism.SA.P


