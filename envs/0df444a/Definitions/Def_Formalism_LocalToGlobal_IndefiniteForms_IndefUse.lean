-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefUse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:11.237807+00:00
-- url     : https://prove2.me/theorems/e542d0d4-2345-4df2-8b28-c5b37da333a8
-- title:
--   Indef Use
-- statement:
--   Definitions and structural lemmas for Indef Use, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace IndefRows
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df)
include S
end IndefRows
namespace IndefCore
variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCore Df0 Df1 Dc Sp N)
include P
end IndefCore
namespace ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)
end ColData
end Formalism.L2.Indef


