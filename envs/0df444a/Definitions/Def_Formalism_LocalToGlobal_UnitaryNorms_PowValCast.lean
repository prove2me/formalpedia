-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
-- name    : Formalism_LocalToGlobal_UnitaryNorms_PowValCast
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:39.750807+00:00
-- url     : https://prove2.me/theorems/a220a2cf-359b-443a-89fc-64bab9bf3033
-- title:
--   Pow Val Cast
-- statement:
--   Definitions and structural lemmas for Pow Val Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/PowValCast.lean

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
namespace Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
section Gauss
variable (q : ℕ) [Fact q.Prime]
def chiQb : MulChar (ZMod q) Qb := (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom Qb)
def psiQb {w : Qb} (hw : IsPrimitiveRoot w q) : AddChar (ZMod q) Qb := AddChar.zmodChar q hw.pow_eq_one
def gaussQb {w : Qb} (hw : IsPrimitiveRoot w q) : Qb := gaussSum (chiQb q) (psiQb q hw)
variable {q}
end Gauss
end Formalism.L2.Host


