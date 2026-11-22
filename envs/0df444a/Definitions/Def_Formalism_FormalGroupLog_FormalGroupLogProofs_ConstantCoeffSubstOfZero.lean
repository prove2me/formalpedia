-- Prove2me | Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- name    : Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:55.245713+00:00
-- url     : https://prove2.me/theorems/cd6ca9f9-7d9b-4cb8-a93b-e66c3859ea36
-- title:
--   Constant Coeff Subst Of Zero
-- statement:
--   Definitions and structural lemmas for Constant Coeff Subst Of Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)
def omegaF : PowerSeries R :=
  MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]
    (MvPowerSeries.pderiv R 1 F.toPowerSeries)
end Formalism.G.LogP
namespace Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)
end Formalism.G.LogP
namespace Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)
def lam : PowerSeries R := PowerSeries.invOfUnit (omegaF F) 1
variable [Algebra ℚ R]
def logF : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else
    algebraMap ℚ R (1 / (n : ℚ)) * PowerSeries.coeff (n - 1) (lam F)
end Formalism.G.LogP
namespace Formalism.G.LogP
variable {R : Type*} [CommRing R]
end Formalism.G.LogP


