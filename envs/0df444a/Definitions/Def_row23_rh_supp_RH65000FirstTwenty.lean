-- Prove2me | Definitions.Def_row23_rh_supp_RH65000FirstTwenty
-- name    : row23_rh_supp_RH65000FirstTwenty
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:20:27.082274+00:00
-- url     : https://prove2.me/theorems/525f848d-dc9a-4c87-b5ad-e1e0df96b17b
-- title:
--   Row 23 RH support: RH65000FirstTwenty
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65000EvaluatorChunks
import Definitions.Def_ArdaRS_Config64
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH65000ExtendedSlab

deriving instance DecidableEq for ArbEcon.Off.Acc
deriving instance DecidableEq for ArbEcon.Off.StO

def testCfg : Cfg := ArbEcon.OrderK.cfg64 1064960025 14
def testOc : OCfg := ⟨49, 0, 96, 2 ^ (96 * 64), 256⟩
def candidate20 : StO := ⟨21, 56161526235350310397, 56161526235350311153, 3899751712662056401, [⟨46395625539740544515, 47644123160185694306, 93840558, 44008129375306781956, 37717951139515404405, 93840555⟩, ⟨66114830647135563662, 98527841017914238821, 220378190, 81975187225034631511, 72082974490321990700, 220378026⟩, ⟨165375424915281993980, 226159782238964996923, 551083638, 182138530643202716727, 156964153740717618074, 551082346⟩, ⟨430967805875949965635, 545403477103792435013, 1431831098, 445522309283502273433, 375341599820153649032, 1431825619⟩, ⟨1157445756924951370326, 1352235255138519306081, 3816541981, 1151733773305912135094, 952206087687075000212, 3816523266⟩, ⟨3178274818488518593576, 3417980272152472967322, 10361798601, 3083967084991667192634, 2503760797294224931469, 10361740962⟩]⟩

/-- The first generated state is verified by the original kernel evaluator. -/
theorem first_twenty_checked : runO testCfg testOc 20 (StO.init testCfg 5) = candidate20 := by
  decide +kernel

end RH65000ExtendedSlab
#print axioms RH65000ExtendedSlab.first_twenty_checked


