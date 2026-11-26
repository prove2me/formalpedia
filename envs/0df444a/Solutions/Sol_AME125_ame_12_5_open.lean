-- Prove2me | solution 1 for AME125.ame_12_5_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:25:16.116821+00:00
-- url     : https://prove2.me/submissions/de875011-3320-4445-972e-d05b58b34f43

module
public import Definitions.Def_AME125_Certificate
public import Definitions.Def_AME125_FormalTarget
public import Theorems.Thm_AME125_ame125State_isAME

set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
namespace AME125
theorem _root_.solution : ExistsAME 12 5 :=
  ⟨ame125State, ame125State_isAME⟩
end AME125
