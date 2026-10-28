-- Prove2me | Definitions.Def_Sensitivity213303_NatTableChecks
-- name    : Sensitivity213303_NatTableChecks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:19:44.153014+00:00
-- url     : https://prove2.me/theorems/bfee9d85-62a0-43a9-ac5a-d0e49aa74bde
-- title:
--   Recursive lower-bound and scaled-dominance checks on integer tables
-- statement:
--   lowerCheck(b,T) recursively tests whether every leaf of a natural-number lookup table T is at least b. dominates(c,A,B) compares two tables to certify A(i)≤cB(i) for every index; paired branches must have equal cut positions, and a constant leaf is compared against both branches of the other table. These executable checks certify the base-profile positivity and the reset inequality between successive periods.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module NatTableChecks; source SHA256 1697051482b0f8234dc028eba3f66c46520034c6c4f61c9091cebfe9a7e6dfeb.

/- Small structural checks for globally ordered piecewise constant tables. -/
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring



set_option autoImplicit false

namespace ThreeBoundNumeric.NatTable



def lowerCheck (bound : ℕ) : NatTable → Bool
  | .leaf v => bound≤v
  | .branch _ left right => lowerCheck bound left && lowerCheck bound right



/-- The two trees use the same cuts whenever both nodes branch. A leaf may
represent an arbitrarily large constant interval. No interval endpoints need
to be supplied or trusted. -/
def dominates (factor : ℕ) : NatTable → NatTable → Bool
  | .leaf a, .leaf b => a≤factor*b
  | .leaf a, .branch _ left right =>
      dominates factor (.leaf a) left && dominates factor (.leaf a) right
  | .branch _ left right, .leaf b =>
      dominates factor left (.leaf b) && dominates factor right (.leaf b)
  | .branch ca la ra, .branch cb lb rb =>
      ca==cb && dominates factor la lb && dominates factor ra rb
termination_by a b => sizeOf a+sizeOf b



end ThreeBoundNumeric.NatTable


