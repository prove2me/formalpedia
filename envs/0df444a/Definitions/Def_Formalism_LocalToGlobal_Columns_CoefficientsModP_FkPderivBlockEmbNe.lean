-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
-- name    : Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:15.157054+00:00
-- url     : https://prove2.me/theorems/69ca4a26-8ca3-4406-bd32-b9e34b54bc0c
-- title:
--   Fk Pderiv Block Emb Ne
-- statement:
--   Definitions and structural lemmas for Fk Pderiv Block Emb Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
namespace Formalism.L2.DIV
open Formalism.BasicNotions
section Ten
variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}
end Ten
section Rat
variable {K : Type} [Field K] (K0 : Subfield K)
end Rat
end Formalism.L2.DIV


