-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
-- name    : Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:39.355398+00:00
-- url     : https://prove2.me/theorems/e71fae33-5b86-43f8-a601-9a627197215c
-- title:
--   Class Sum Lemmas
-- statement:
--   Definitions and structural lemmas for Class Sum Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
end Formalism.L2.DIV.CSD


