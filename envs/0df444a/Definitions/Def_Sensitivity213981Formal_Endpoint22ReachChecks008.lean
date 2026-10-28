-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks008
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks008
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:09.91066+00:00
-- url     : https://prove2.me/theorems/a5ad250a-58ef-41d5-816b-99be240d3bf5
-- title:
--   Endpoint22 Reach Checks008 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks008 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_372root`, `ThreeBoundEndpoint22Reachable.t5_372jobs0`, `ThreeBoundEndpoint22Reachable.t5_372jobs`, `ThreeBoundEndpoint22Reachable.t5_373root`, `ThreeBoundEndpoint22Reachable.t5_373jobs0`, `ThreeBoundEndpoint22Reachable.t5_373jobs`, `ThreeBoundEndpoint22Reachable.t5_374root`, `ThreeBoundEndpoint22Reachable.t5_374jobs0`, `ThreeBoundEndpoint22Reachable.t5_374jobs`, `ThreeBoundEndpoint22Reachable.t5_375root`, `ThreeBoundEndpoint22Reachable.t5_375jobs0`, `ThreeBoundEndpoint22Reachable.t5_375jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks008.lean, lines 1–381.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans042
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
open ThreeBoundEndpoint22Packed (tree)

def t5_359root : Job := ⟨plan3854,[],none,⟨10,1,0⟩⟩
def t5_359jobs0 : List Job := [⟨plan2614,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2614,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_359jobs1 : List Job := [⟨plan2614,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_359jobs : List Job := t5_359jobs0++t5_359jobs1




def t5_360root : Job := ⟨plan3855,[],none,⟨10,1,0⟩⟩
def t5_360jobs0 : List Job := [⟨plan3855,[],none,⟨10,1,0⟩⟩]

def t5_360jobs : List Job := t5_360jobs0




def t5_361root : Job := ⟨plan3715,[],none,⟨10,0,0⟩⟩
def t5_361jobs0 : List Job := [⟨plan3715,[],none,⟨10,0,0⟩⟩]

def t5_361jobs : List Job := t5_361jobs0




def t5_362root : Job := ⟨plan3856,[],none,⟨10,1,0⟩⟩
def t5_362jobs0 : List Job := [⟨plan3856,[],none,⟨10,1,0⟩⟩]

def t5_362jobs : List Job := t5_362jobs0




def t5_363root : Job := ⟨plan3857,[],none,⟨10,1,0⟩⟩
def t5_363jobs0 : List Job := [⟨plan3857,[],none,⟨10,1,0⟩⟩]

def t5_363jobs : List Job := t5_363jobs0




def t5_364root : Job := ⟨plan3858,[],none,⟨10,1,0⟩⟩
def t5_364jobs0 : List Job := [⟨plan3858,[],none,⟨10,1,0⟩⟩]

def t5_364jobs : List Job := t5_364jobs0




def t5_365root : Job := ⟨plan3859,[],none,⟨10,1,0⟩⟩
def t5_365jobs0 : List Job := [⟨plan3859,[],none,⟨10,1,0⟩⟩]

def t5_365jobs : List Job := t5_365jobs0




def t5_366root : Job := ⟨plan4125,[],none,⟨10,3,0⟩⟩
def t5_366jobs0 : List Job := [⟨plan4125,[],none,⟨10,3,0⟩⟩]

def t5_366jobs : List Job := t5_366jobs0




def t5_367root : Job := ⟨plan4126,[],none,⟨10,3,0⟩⟩
def t5_367jobs0 : List Job := [⟨plan4126,[],none,⟨10,3,0⟩⟩]

def t5_367jobs : List Job := t5_367jobs0




def t5_368root : Job := ⟨plan4127,[],none,⟨10,3,0⟩⟩
def t5_368jobs0 : List Job := [⟨plan4127,[],none,⟨10,3,0⟩⟩]

def t5_368jobs : List Job := t5_368jobs0




def t5_369root : Job := ⟨plan4128,[],none,⟨10,3,0⟩⟩
def t5_369jobs0 : List Job := [⟨plan4128,[],none,⟨10,3,0⟩⟩]

def t5_369jobs : List Job := t5_369jobs0




def t5_370root : Job := ⟨plan4129,[],none,⟨10,3,0⟩⟩
def t5_370jobs0 : List Job := [⟨plan4129,[],none,⟨10,3,0⟩⟩]

def t5_370jobs : List Job := t5_370jobs0




def t5_371root : Job := ⟨plan4130,[],none,⟨10,3,0⟩⟩
def t5_371jobs0 : List Job := [⟨plan4130,[],none,⟨10,3,0⟩⟩]

def t5_371jobs : List Job := t5_371jobs0




def t5_372root : Job := ⟨plan4131,[],none,⟨10,3,0⟩⟩
def t5_372jobs0 : List Job := [⟨plan4131,[],none,⟨10,3,0⟩⟩]

def t5_372jobs : List Job := t5_372jobs0




def t5_373root : Job := ⟨plan3860,[],none,⟨10,1,0⟩⟩
def t5_373jobs0 : List Job := [⟨plan3860,[],none,⟨10,1,0⟩⟩]

def t5_373jobs : List Job := t5_373jobs0




def t5_374root : Job := ⟨plan4132,[],none,⟨10,3,0⟩⟩
def t5_374jobs0 : List Job := [⟨plan4132,[],none,⟨10,3,0⟩⟩]

def t5_374jobs : List Job := t5_374jobs0




def t5_375root : Job := ⟨plan4133,[],none,⟨10,3,0⟩⟩
def t5_375jobs0 : List Job := [⟨plan4133,[],none,⟨10,3,0⟩⟩]

def t5_375jobs : List Job := t5_375jobs0




def t5_376root : Job := ⟨plan4134,[],none,⟨10,3,0⟩⟩
def t5_376jobs0 : List Job := [⟨plan4134,[],none,⟨10,3,0⟩⟩]

def t5_376jobs : List Job := t5_376jobs0




def t5_377root : Job := ⟨plan4135,[],none,⟨10,3,0⟩⟩
def t5_377jobs0 : List Job := [⟨plan4135,[],none,⟨10,3,0⟩⟩]

def t5_377jobs : List Job := t5_377jobs0




def t5_378root : Job := ⟨plan4136,[],none,⟨10,3,0⟩⟩
def t5_378jobs0 : List Job := [⟨plan4136,[],none,⟨10,3,0⟩⟩]

def t5_378jobs : List Job := t5_378jobs0




def t5_379root : Job := ⟨plan4137,[],none,⟨10,3,0⟩⟩
def t5_379jobs0 : List Job := [⟨plan4137,[],none,⟨10,3,0⟩⟩]

def t5_379jobs : List Job := t5_379jobs0




def t5_380root : Job := ⟨plan4138,[],none,⟨10,3,0⟩⟩
def t5_380jobs0 : List Job := [⟨plan4138,[],none,⟨10,3,0⟩⟩]

def t5_380jobs : List Job := t5_380jobs0




def t5_381root : Job := ⟨plan4139,[],none,⟨10,3,0⟩⟩
def t5_381jobs0 : List Job := [⟨plan4139,[],none,⟨10,3,0⟩⟩]

def t5_381jobs : List Job := t5_381jobs0




def t5_382root : Job := ⟨plan4140,[],none,⟨10,3,0⟩⟩
def t5_382jobs0 : List Job := [⟨plan4140,[],none,⟨10,3,0⟩⟩]

def t5_382jobs : List Job := t5_382jobs0




def t5_383root : Job := ⟨plan4141,[],none,⟨10,3,0⟩⟩
def t5_383jobs0 : List Job := [⟨plan2742,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2742,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_383jobs1 : List Job := [⟨plan2742,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_383jobs : List Job := t5_383jobs0++t5_383jobs1




def t5_384root : Job := ⟨plan4142,[],none,⟨10,3,0⟩⟩
def t5_384jobs0 : List Job := [⟨plan4142,[],none,⟨10,3,0⟩⟩]

def t5_384jobs : List Job := t5_384jobs0




def t5_385root : Job := ⟨plan4143,[],none,⟨10,3,0⟩⟩
def t5_385jobs0 : List Job := [⟨plan4143,[],none,⟨10,3,0⟩⟩]

def t5_385jobs : List Job := t5_385jobs0




def t5_386root : Job := ⟨plan3716,[],none,⟨10,0,0⟩⟩
def t5_386jobs0 : List Job := [⟨plan3716,[],none,⟨10,0,0⟩⟩]

def t5_386jobs : List Job := t5_386jobs0




def t5_387root : Job := ⟨plan3861,[],none,⟨10,1,0⟩⟩
def t5_387jobs0 : List Job := [⟨plan3861,[],none,⟨10,1,0⟩⟩]

def t5_387jobs : List Job := t5_387jobs0




def t5_388root : Job := ⟨plan3862,[],none,⟨10,1,0⟩⟩
def t5_388jobs0 : List Job := [⟨plan3862,[],none,⟨10,1,0⟩⟩]

def t5_388jobs : List Job := t5_388jobs0




def t5_389root : Job := ⟨plan3863,[],none,⟨10,1,0⟩⟩
def t5_389jobs0 : List Job := [⟨plan3863,[],none,⟨10,1,0⟩⟩]

def t5_389jobs : List Job := t5_389jobs0




def t5_390root : Job := ⟨plan4144,[],none,⟨10,3,0⟩⟩
def t5_390jobs0 : List Job := [⟨plan4144,[],none,⟨10,3,0⟩⟩]

def t5_390jobs : List Job := t5_390jobs0




def t5_391root : Job := ⟨plan4145,[],none,⟨10,3,0⟩⟩
def t5_391jobs0 : List Job := [⟨plan4145,[],none,⟨10,3,0⟩⟩]

def t5_391jobs : List Job := t5_391jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


