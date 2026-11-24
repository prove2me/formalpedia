-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:26.949858+00:00
-- url     : https://prove2.me/theorems/2ee32fca-bb7f-4b52-9505-fd6306cbb22c
-- title:
--   Fr Tan Dir Alg
-- statement:
--   Definitions and structural lemmas for Fr Tan Dir Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrTanDirAlg.lean

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
section Core
variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]
end Core
section NT
variable (E : Type) [Field E] [NumberField E]
end NT
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg


