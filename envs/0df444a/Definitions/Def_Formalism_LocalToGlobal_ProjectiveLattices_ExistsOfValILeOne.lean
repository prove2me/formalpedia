-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:18.560481+00:00
-- url     : https://prove2.me/theorems/754700af-11c5-46cd-ac4d-18455036683a
-- title:
--   Exists Of Val ILe One
-- statement:
--   Definitions and structural lemmas for Exists Of Val ILe One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ExistsOfValILeOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
variable (V) in

abbrev valI : Valuation F (WithZero (Multiplicative ℤ)) := (IsDiscreteValuationRing.maximalIdeal V).valuation F
end Formalism.L2.Pj


