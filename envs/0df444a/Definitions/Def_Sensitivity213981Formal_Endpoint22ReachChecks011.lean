-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks011
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks011
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:27.583491+00:00
-- url     : https://prove2.me/theorems/478ff00b-4775-4476-aaaf-7a383c70b8e0
-- title:
--   Endpoint22 Reach Checks011 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks011 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_479jobs0`, `ThreeBoundEndpoint22Reachable.t5_479jobs`, `ThreeBoundEndpoint22Reachable.t5_480root`, `ThreeBoundEndpoint22Reachable.t5_480jobs0`, `ThreeBoundEndpoint22Reachable.t5_480jobs`, `ThreeBoundEndpoint22Reachable.t5_481root`, `ThreeBoundEndpoint22Reachable.t5_481jobs0`, `ThreeBoundEndpoint22Reachable.t5_481jobs`, `ThreeBoundEndpoint22Reachable.t5_482root`, `ThreeBoundEndpoint22Reachable.t5_482jobs0`, `ThreeBoundEndpoint22Reachable.t5_482jobs`, `ThreeBoundEndpoint22Reachable.t5_467root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks011.lean, lines 1–583.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
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

def t5_466root : Job := ⟨plan4554,[],none,⟨10,6,0⟩⟩
def t5_466jobs0 : List Job := [⟨plan4554,[],none,⟨10,6,0⟩⟩]

def t5_466jobs : List Job := t5_466jobs0




def t5_467root : Job := ⟨plan4555,[],none,⟨10,6,0⟩⟩
def t5_467jobs0 : List Job := [⟨plan4555,[],none,⟨10,6,0⟩⟩]

def t5_467jobs : List Job := t5_467jobs0




def t5_468root : Job := ⟨plan4556,[],none,⟨10,6,0⟩⟩
def t5_468jobs0 : List Job := [⟨plan4556,[],none,⟨10,6,0⟩⟩]

def t5_468jobs : List Job := t5_468jobs0




def t5_469root : Job := ⟨plan4184,[],none,⟨10,3,0⟩⟩
def t5_469jobs0 : List Job := [⟨plan4184,[],none,⟨10,3,0⟩⟩]

def t5_469jobs : List Job := t5_469jobs0




def t5_470root : Job := ⟨plan4557,[],none,⟨10,6,0⟩⟩
def t5_470jobs0 : List Job := [⟨plan4557,[],none,⟨10,6,0⟩⟩]

def t5_470jobs : List Job := t5_470jobs0




def t5_471root : Job := ⟨plan4558,[],none,⟨10,6,0⟩⟩
def t5_471jobs0 : List Job := [⟨plan4558,[],none,⟨10,6,0⟩⟩]

def t5_471jobs : List Job := t5_471jobs0




def t5_472root : Job := ⟨plan4559,[],none,⟨10,6,0⟩⟩
def t5_472jobs0 : List Job := [⟨plan4559,[],none,⟨10,6,0⟩⟩]

def t5_472jobs : List Job := t5_472jobs0




def t5_473root : Job := ⟨plan3879,[],none,⟨10,1,0⟩⟩
def t5_473jobs0 : List Job := [⟨plan3879,[],none,⟨10,1,0⟩⟩]

def t5_473jobs : List Job := t5_473jobs0




def t5_474root : Job := ⟨plan4185,[],none,⟨10,3,0⟩⟩
def t5_474jobs0 : List Job := [⟨plan4185,[],none,⟨10,3,0⟩⟩]

def t5_474jobs : List Job := t5_474jobs0




def t5_475root : Job := ⟨plan4186,[],none,⟨10,3,0⟩⟩
def t5_475jobs0 : List Job := [⟨plan4186,[],none,⟨10,3,0⟩⟩]

def t5_475jobs : List Job := t5_475jobs0




def t5_476root : Job := ⟨plan4187,[],none,⟨10,3,0⟩⟩
def t5_476jobs0 : List Job := [⟨plan4187,[],none,⟨10,3,0⟩⟩]

def t5_476jobs : List Job := t5_476jobs0




def t5_477root : Job := ⟨plan4560,[],none,⟨10,6,0⟩⟩
def t5_477jobs0 : List Job := [⟨plan4560,[],none,⟨10,6,0⟩⟩]

def t5_477jobs : List Job := t5_477jobs0




def t5_478root : Job := ⟨plan4561,[],none,⟨10,6,0⟩⟩
def t5_478jobs0 : List Job := [⟨plan4561,[],none,⟨10,6,0⟩⟩]

def t5_478jobs : List Job := t5_478jobs0




def t5_479root : Job := ⟨plan4562,[],none,⟨10,6,0⟩⟩
def t5_479jobs0 : List Job := [⟨plan4562,[],none,⟨10,6,0⟩⟩]

def t5_479jobs : List Job := t5_479jobs0




def t5_480root : Job := ⟨plan4563,[],none,⟨10,6,0⟩⟩
def t5_480jobs0 : List Job := [⟨plan4563,[],none,⟨10,6,0⟩⟩]

def t5_480jobs : List Job := t5_480jobs0




def t5_481root : Job := ⟨plan4564,[],none,⟨10,6,0⟩⟩
def t5_481jobs0 : List Job := [⟨plan4564,[],none,⟨10,6,0⟩⟩]

def t5_481jobs : List Job := t5_481jobs0




def t5_482root : Job := ⟨plan4565,[],none,⟨10,6,0⟩⟩
def t5_482jobs0 : List Job := [⟨plan4565,[],none,⟨10,6,0⟩⟩]

def t5_482jobs : List Job := t5_482jobs0




def t5_483root : Job := ⟨plan4566,[],none,⟨10,6,0⟩⟩
def t5_483jobs0 : List Job := [⟨plan4566,[],none,⟨10,6,0⟩⟩]

def t5_483jobs : List Job := t5_483jobs0




def t5_484root : Job := ⟨plan4567,[],none,⟨10,6,0⟩⟩
def t5_484jobs0 : List Job := [⟨plan4567,[],none,⟨10,6,0⟩⟩]

def t5_484jobs : List Job := t5_484jobs0




def t5_485root : Job := ⟨plan4568,[],none,⟨10,6,0⟩⟩
def t5_485jobs0 : List Job := [⟨plan4568,[],none,⟨10,6,0⟩⟩]

def t5_485jobs : List Job := t5_485jobs0




def t5_486root : Job := ⟨plan4569,[],none,⟨10,6,0⟩⟩
def t5_486jobs0 : List Job := [⟨plan4569,[],none,⟨10,6,0⟩⟩]

def t5_486jobs : List Job := t5_486jobs0




def t5_487root : Job := ⟨plan3722,[],none,⟨10,0,0⟩⟩
def t5_487jobs0 : List Job := [⟨plan3722,[],none,⟨10,0,0⟩⟩]

def t5_487jobs : List Job := t5_487jobs0




def t5_488root : Job := ⟨plan3880,[],none,⟨10,1,0⟩⟩
def t5_488jobs0 : List Job := [⟨plan3880,[],none,⟨10,1,0⟩⟩]

def t5_488jobs : List Job := t5_488jobs0




def t5_489root : Job := ⟨plan3881,[],none,⟨10,1,0⟩⟩
def t5_489jobs0 : List Job := [⟨plan3881,[],none,⟨10,1,0⟩⟩]

def t5_489jobs : List Job := t5_489jobs0




def t5_490root : Job := ⟨plan3882,[],none,⟨10,1,0⟩⟩
def t5_490jobs0 : List Job := [⟨plan3882,[],none,⟨10,1,0⟩⟩]

def t5_490jobs : List Job := t5_490jobs0




def t5_491root : Job := ⟨plan4188,[],none,⟨10,3,0⟩⟩
def t5_491jobs0 : List Job := [⟨plan4188,[],none,⟨10,3,0⟩⟩]

def t5_491jobs : List Job := t5_491jobs0




def t5_492root : Job := ⟨plan4189,[],none,⟨10,3,0⟩⟩
def t5_492jobs0 : List Job := [⟨plan2813,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2813,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_492jobs1 : List Job := [⟨plan2813,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_492jobs : List Job := t5_492jobs0++t5_492jobs1




def t5_493root : Job := ⟨plan4190,[],none,⟨10,3,0⟩⟩
def t5_493jobs0 : List Job := [⟨plan2814,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2814,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_493jobs1 : List Job := [⟨plan2814,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_493jobs : List Job := t5_493jobs0++t5_493jobs1




def t5_494root : Job := ⟨plan4191,[],none,⟨10,3,0⟩⟩
def t5_494jobs0 : List Job := [⟨plan2815,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2815,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_494jobs1 : List Job := [⟨plan2815,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_494jobs : List Job := t5_494jobs0++t5_494jobs1




def t5_495root : Job := ⟨plan4192,[],none,⟨10,3,0⟩⟩
def t5_495jobs0 : List Job := [⟨plan2816,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2816,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_495jobs1 : List Job := [⟨plan2816,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_495jobs : List Job := t5_495jobs0++t5_495jobs1




def t5_496root : Job := ⟨plan4193,[],none,⟨10,3,0⟩⟩
def t5_496jobs0 : List Job := [⟨plan4193,[],none,⟨10,3,0⟩⟩]

def t5_496jobs : List Job := t5_496jobs0




def t5_497root : Job := ⟨plan3883,[],none,⟨10,1,0⟩⟩
def t5_497jobs0 : List Job := [⟨plan3883,[],none,⟨10,1,0⟩⟩]

def t5_497jobs : List Job := t5_497jobs0




def t5_498root : Job := ⟨plan4194,[],none,⟨10,3,0⟩⟩
def t5_498jobs0 : List Job := [⟨plan4194,[],none,⟨10,3,0⟩⟩]

def t5_498jobs : List Job := t5_498jobs0




def t5_499root : Job := ⟨plan4195,[],none,⟨10,3,0⟩⟩
def t5_499jobs0 : List Job := [⟨plan4195,[],none,⟨10,3,0⟩⟩]

def t5_499jobs : List Job := t5_499jobs0




def t5_500root : Job := ⟨plan4196,[],none,⟨10,3,0⟩⟩
def t5_500jobs0 : List Job := [⟨plan4196,[],none,⟨10,3,0⟩⟩]

def t5_500jobs : List Job := t5_500jobs0




def t5_501root : Job := ⟨plan4197,[],none,⟨10,3,0⟩⟩
def t5_501jobs0 : List Job := [⟨plan4197,[],none,⟨10,3,0⟩⟩]

def t5_501jobs : List Job := t5_501jobs0




def t5_502root : Job := ⟨plan4570,[],none,⟨10,6,0⟩⟩
def t5_502jobs0 : List Job := [⟨plan4570,[],none,⟨10,6,0⟩⟩]

def t5_502jobs : List Job := t5_502jobs0




def t5_503root : Job := ⟨plan4571,[],none,⟨10,6,0⟩⟩
def t5_503jobs0 : List Job := [⟨plan4571,[],none,⟨10,6,0⟩⟩]

def t5_503jobs : List Job := t5_503jobs0




def t5_504root : Job := ⟨plan4572,[],none,⟨10,6,0⟩⟩
def t5_504jobs0 : List Job := [⟨plan4572,[],none,⟨10,6,0⟩⟩]

def t5_504jobs : List Job := t5_504jobs0




def t5_505root : Job := ⟨plan4573,[],none,⟨10,6,0⟩⟩
def t5_505jobs0 : List Job := [⟨plan4573,[],none,⟨10,6,0⟩⟩]

def t5_505jobs : List Job := t5_505jobs0




def t5_506root : Job := ⟨plan4574,[],none,⟨10,6,0⟩⟩
def t5_506jobs0 : List Job := [⟨plan4574,[],none,⟨10,6,0⟩⟩]

def t5_506jobs : List Job := t5_506jobs0




def t5_507root : Job := ⟨plan4575,[],none,⟨10,6,0⟩⟩
def t5_507jobs0 : List Job := [⟨plan4575,[],none,⟨10,6,0⟩⟩]

def t5_507jobs : List Job := t5_507jobs0




def t5_508root : Job := ⟨plan4576,[],none,⟨10,6,0⟩⟩
def t5_508jobs0 : List Job := [⟨plan4576,[],none,⟨10,6,0⟩⟩]

def t5_508jobs : List Job := t5_508jobs0




def t5_509root : Job := ⟨plan4198,[],none,⟨10,3,0⟩⟩
def t5_509jobs0 : List Job := [⟨plan4198,[],none,⟨10,3,0⟩⟩]

def t5_509jobs : List Job := t5_509jobs0




def t5_510root : Job := ⟨plan4577,[],none,⟨10,6,0⟩⟩
def t5_510jobs0 : List Job := [⟨plan4577,[],none,⟨10,6,0⟩⟩]

def t5_510jobs : List Job := t5_510jobs0




def t5_511root : Job := ⟨plan4578,[],none,⟨10,6,0⟩⟩
def t5_511jobs0 : List Job := [⟨plan4578,[],none,⟨10,6,0⟩⟩]

def t5_511jobs : List Job := t5_511jobs0




def t5_512root : Job := ⟨plan4579,[],none,⟨10,6,0⟩⟩
def t5_512jobs0 : List Job := [⟨plan4579,[],none,⟨10,6,0⟩⟩]

def t5_512jobs : List Job := t5_512jobs0




def t5_513root : Job := ⟨plan4580,[],none,⟨10,6,0⟩⟩
def t5_513jobs0 : List Job := [⟨plan4580,[],none,⟨10,6,0⟩⟩]

def t5_513jobs : List Job := t5_513jobs0




def t5_514root : Job := ⟨plan4581,[],none,⟨10,6,0⟩⟩
def t5_514jobs0 : List Job := [⟨plan4581,[],none,⟨10,6,0⟩⟩]

def t5_514jobs : List Job := t5_514jobs0




def t5_515root : Job := ⟨plan4582,[],none,⟨10,6,0⟩⟩
def t5_515jobs0 : List Job := [⟨plan4582,[],none,⟨10,6,0⟩⟩]

def t5_515jobs : List Job := t5_515jobs0




def t5_516root : Job := ⟨plan4583,[],none,⟨10,6,0⟩⟩
def t5_516jobs0 : List Job := [⟨plan4583,[],none,⟨10,6,0⟩⟩]

def t5_516jobs : List Job := t5_516jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


