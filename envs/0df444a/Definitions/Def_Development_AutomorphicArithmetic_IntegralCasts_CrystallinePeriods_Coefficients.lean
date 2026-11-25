-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:52.503931+00:00
-- url     : https://prove2.me/theorems/b88b80ba-91a8-422c-b374-c81c4625a21f
-- title:
--   Coefficients
-- statement:
--   Definitions and structural lemmas for Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Theorems.Thm_Reformulated_AutPerF_Bcris_isUnit_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
def BcrisPlus.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* BcrisPlus p R :=
  fracWittLift p ((algebraMap (Acris p R) (BcrisPlus p R)).comp
    ((algebraMap (Ainf p R) (Acris p R)).comp (Ainf.liftWitt p g))) (BcrisPlus.isUnit_p p R)
variable {p}
end Reformulated.AutPerF


