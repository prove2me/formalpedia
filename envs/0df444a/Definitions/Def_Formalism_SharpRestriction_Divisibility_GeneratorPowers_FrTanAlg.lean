-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:31.133923+00:00
-- url     : https://prove2.me/theorems/928e54df-e7ac-4158-8745-0bd0166e7206
-- title:
--   Fr Tan Alg
-- statement:
--   Definitions and structural lemmas for Fr Tan Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanAlg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
section Eig
variable {S M : Type} [Field S] [AddCommGroup M] [Module S M]
end Eig
section Prim
variable (E : Type) [Field E] [NumberField E]
end Prim
section Decomp
variable {E : Type} [Field E] [NumberField E] {S M : Type} [Field S] [CharZero S] [AddCommGroup M] [Module S M]
  {ι : Type} [Fintype ι] [DecidableEq ι]
end Decomp
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg


