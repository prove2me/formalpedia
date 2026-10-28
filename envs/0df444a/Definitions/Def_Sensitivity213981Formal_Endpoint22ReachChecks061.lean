-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks061
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks061
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:04.666979+00:00
-- url     : https://prove2.me/theorems/6277caf7-ade7-491f-bf78-f27b2d75c550
-- title:
--   Endpoint22 Reach Checks061 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks061 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_500root`, `ThreeBoundEndpoint22Reachable.t6_500jobs0`, `ThreeBoundEndpoint22Reachable.t6_500jobs`, `ThreeBoundEndpoint22Reachable.t6_501root`, `ThreeBoundEndpoint22Reachable.t6_501jobs0`, `ThreeBoundEndpoint22Reachable.t6_501jobs`, `ThreeBoundEndpoint22Reachable.t6_502root`, `ThreeBoundEndpoint22Reachable.t6_502jobs0`, `ThreeBoundEndpoint22Reachable.t6_502jobs`, `ThreeBoundEndpoint22Reachable.t6_503root`, `ThreeBoundEndpoint22Reachable.t6_503jobs0`, `ThreeBoundEndpoint22Reachable.t6_503jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks061.lean, lines 1–609.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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

def t6_487root : Job := ⟨plan7299,[],none,⟨15,10,0⟩⟩
def t6_487jobs0 : List Job := [⟨plan7299,[],none,⟨15,10,0⟩⟩]

def t6_487jobs : List Job := t6_487jobs0




def t6_488root : Job := ⟨plan7300,[],none,⟨15,10,0⟩⟩
def t6_488jobs0 : List Job := [⟨plan7300,[],none,⟨15,10,0⟩⟩]

def t6_488jobs : List Job := t6_488jobs0




def t6_489root : Job := ⟨plan7301,[],none,⟨15,10,0⟩⟩
def t6_489jobs0 : List Job := [⟨plan7301,[],none,⟨15,10,0⟩⟩]

def t6_489jobs : List Job := t6_489jobs0




def t6_490root : Job := ⟨plan7302,[],none,⟨15,10,0⟩⟩
def t6_490jobs0 : List Job := [⟨plan7302,[],none,⟨15,10,0⟩⟩]

def t6_490jobs : List Job := t6_490jobs0




def t6_491root : Job := ⟨plan7303,[],none,⟨15,10,0⟩⟩
def t6_491jobs0 : List Job := [⟨plan7303,[],none,⟨15,10,0⟩⟩]

def t6_491jobs : List Job := t6_491jobs0




def t6_492root : Job := ⟨plan6535,[],none,⟨15,3,0⟩⟩
def t6_492jobs0 : List Job := [⟨plan6535,[],none,⟨15,3,0⟩⟩]

def t6_492jobs : List Job := t6_492jobs0




def t6_493root : Job := ⟨plan6867,[],none,⟨15,6,0⟩⟩
def t6_493jobs0 : List Job := [⟨plan6867,[],none,⟨15,6,0⟩⟩]

def t6_493jobs : List Job := t6_493jobs0




def t6_494root : Job := ⟨plan6868,[],none,⟨15,6,0⟩⟩
def t6_494jobs0 : List Job := [⟨plan6868,[],none,⟨15,6,0⟩⟩]

def t6_494jobs : List Job := t6_494jobs0




def t6_495root : Job := ⟨plan6869,[],none,⟨15,6,0⟩⟩
def t6_495jobs0 : List Job := [⟨plan6869,[],none,⟨15,6,0⟩⟩]

def t6_495jobs : List Job := t6_495jobs0




def t6_496root : Job := ⟨plan7304,[],none,⟨15,10,0⟩⟩
def t6_496jobs0 : List Job := [⟨plan7304,[],none,⟨15,10,0⟩⟩]

def t6_496jobs : List Job := t6_496jobs0




def t6_497root : Job := ⟨plan7305,[],none,⟨15,10,0⟩⟩
def t6_497jobs0 : List Job := [⟨plan7305,[],none,⟨15,10,0⟩⟩]

def t6_497jobs : List Job := t6_497jobs0




def t6_498root : Job := ⟨plan7306,[],none,⟨15,10,0⟩⟩
def t6_498jobs0 : List Job := [⟨plan7306,[],none,⟨15,10,0⟩⟩]

def t6_498jobs : List Job := t6_498jobs0




def t6_499root : Job := ⟨plan7307,[],none,⟨15,10,0⟩⟩
def t6_499jobs0 : List Job := [⟨plan7307,[],none,⟨15,10,0⟩⟩]

def t6_499jobs : List Job := t6_499jobs0




def t6_500root : Job := ⟨plan7308,[],none,⟨15,10,0⟩⟩
def t6_500jobs0 : List Job := [⟨plan7308,[],none,⟨15,10,0⟩⟩]

def t6_500jobs : List Job := t6_500jobs0




def t6_501root : Job := ⟨plan7309,[],none,⟨15,10,0⟩⟩
def t6_501jobs0 : List Job := [⟨plan7309,[],none,⟨15,10,0⟩⟩]

def t6_501jobs : List Job := t6_501jobs0




def t6_502root : Job := ⟨plan7310,[],none,⟨15,10,0⟩⟩
def t6_502jobs0 : List Job := [⟨plan7310,[],none,⟨15,10,0⟩⟩]

def t6_502jobs : List Job := t6_502jobs0




def t6_503root : Job := ⟨plan7311,[],none,⟨15,10,0⟩⟩
def t6_503jobs0 : List Job := [⟨plan7311,[],none,⟨15,10,0⟩⟩]

def t6_503jobs : List Job := t6_503jobs0




def t6_504root : Job := ⟨plan7312,[],none,⟨15,10,0⟩⟩
def t6_504jobs0 : List Job := [⟨plan7312,[],none,⟨15,10,0⟩⟩]

def t6_504jobs : List Job := t6_504jobs0




def t6_505root : Job := ⟨plan7313,[],none,⟨15,10,0⟩⟩
def t6_505jobs0 : List Job := [⟨plan7313,[],none,⟨15,10,0⟩⟩]

def t6_505jobs : List Job := t6_505jobs0




def t6_506root : Job := ⟨plan7314,[],none,⟨15,10,0⟩⟩
def t6_506jobs0 : List Job := [⟨plan7314,[],none,⟨15,10,0⟩⟩]

def t6_506jobs : List Job := t6_506jobs0




def t6_507root : Job := ⟨plan7315,[],none,⟨15,10,0⟩⟩
def t6_507jobs0 : List Job := [⟨plan7315,[],none,⟨15,10,0⟩⟩]

def t6_507jobs : List Job := t6_507jobs0




def t6_508root : Job := ⟨plan7316,[],none,⟨15,10,0⟩⟩
def t6_508jobs0 : List Job := [⟨plan7316,[],none,⟨15,10,0⟩⟩]

def t6_508jobs : List Job := t6_508jobs0




def t6_509root : Job := ⟨plan7317,[],none,⟨15,10,0⟩⟩
def t6_509jobs0 : List Job := [⟨plan7317,[],none,⟨15,10,0⟩⟩]

def t6_509jobs : List Job := t6_509jobs0




def t6_510root : Job := ⟨plan7318,[],none,⟨15,10,0⟩⟩
def t6_510jobs0 : List Job := [⟨plan7318,[],none,⟨15,10,0⟩⟩]

def t6_510jobs : List Job := t6_510jobs0




def t6_511root : Job := ⟨plan7319,[],none,⟨15,10,0⟩⟩
def t6_511jobs0 : List Job := [⟨plan7319,[],none,⟨15,10,0⟩⟩]

def t6_511jobs : List Job := t6_511jobs0




def t6_512root : Job := ⟨plan6297,[],none,⟨15,0,0⟩⟩
def t6_512jobs0 : List Job := [⟨plan6297,[],none,⟨15,0,0⟩⟩]

def t6_512jobs : List Job := t6_512jobs0




def t6_513root : Job := ⟨plan6363,[],none,⟨15,1,0⟩⟩
def t6_513jobs0 : List Job := [⟨plan6363,[],none,⟨15,1,0⟩⟩]

def t6_513jobs : List Job := t6_513jobs0




def t6_514root : Job := ⟨plan6364,[],none,⟨15,1,0⟩⟩
def t6_514jobs0 : List Job := [⟨plan6364,[],none,⟨15,1,0⟩⟩]

def t6_514jobs : List Job := t6_514jobs0




def t6_515root : Job := ⟨plan6365,[],none,⟨15,1,0⟩⟩
def t6_515jobs0 : List Job := [⟨plan6365,[],none,⟨15,1,0⟩⟩]

def t6_515jobs : List Job := t6_515jobs0




def t6_516root : Job := ⟨plan6279,[],none,⟨15,0,0⟩⟩
def t6_516jobs0 : List Job := [⟨plan6279,[],none,⟨15,0,0⟩⟩]

def t6_516jobs : List Job := t6_516jobs0




def t6_517root : Job := ⟨plan6298,[],none,⟨15,0,0⟩⟩
def t6_517jobs0 : List Job := [⟨plan6298,[],none,⟨15,0,0⟩⟩]

def t6_517jobs : List Job := t6_517jobs0




def t6_518root : Job := ⟨plan6299,[],none,⟨15,0,0⟩⟩
def t6_518jobs0 : List Job := [⟨plan6299,[],none,⟨15,0,0⟩⟩]

def t6_518jobs : List Job := t6_518jobs0




def t6_519root : Job := ⟨plan6300,[],none,⟨15,0,0⟩⟩
def t6_519jobs0 : List Job := [⟨plan6300,[],none,⟨15,0,0⟩⟩]

def t6_519jobs : List Job := t6_519jobs0




def t6_520root : Job := ⟨plan6366,[],none,⟨15,1,0⟩⟩
def t6_520jobs0 : List Job := [⟨plan6366,[],none,⟨15,1,0⟩⟩]

def t6_520jobs : List Job := t6_520jobs0




def t6_521root : Job := ⟨plan6367,[],none,⟨15,1,0⟩⟩
def t6_521jobs0 : List Job := [⟨plan6367,[],none,⟨15,1,0⟩⟩]

def t6_521jobs : List Job := t6_521jobs0




def t6_522root : Job := ⟨plan6368,[],none,⟨15,1,0⟩⟩
def t6_522jobs0 : List Job := [⟨plan6368,[],none,⟨15,1,0⟩⟩]

def t6_522jobs : List Job := t6_522jobs0




def t6_523root : Job := ⟨plan6369,[],none,⟨15,1,0⟩⟩
def t6_523jobs0 : List Job := [⟨plan6369,[],none,⟨15,1,0⟩⟩]

def t6_523jobs : List Job := t6_523jobs0




def t6_524root : Job := ⟨plan6370,[],none,⟨15,1,0⟩⟩
def t6_524jobs0 : List Job := [⟨plan6370,[],none,⟨15,1,0⟩⟩]

def t6_524jobs : List Job := t6_524jobs0




def t6_525root : Job := ⟨plan6371,[],none,⟨15,1,0⟩⟩
def t6_525jobs0 : List Job := [⟨plan6371,[],none,⟨15,1,0⟩⟩]

def t6_525jobs : List Job := t6_525jobs0




def t6_526root : Job := ⟨plan6372,[],none,⟨15,1,0⟩⟩
def t6_526jobs0 : List Job := [⟨plan6372,[],none,⟨15,1,0⟩⟩]

def t6_526jobs : List Job := t6_526jobs0




def t6_527root : Job := ⟨plan6536,[],none,⟨15,3,0⟩⟩
def t6_527jobs0 : List Job := [⟨plan6536,[],none,⟨15,3,0⟩⟩]

def t6_527jobs : List Job := t6_527jobs0




def t6_528root : Job := ⟨plan6537,[],none,⟨15,3,0⟩⟩
def t6_528jobs0 : List Job := [⟨plan6537,[],none,⟨15,3,0⟩⟩]

def t6_528jobs : List Job := t6_528jobs0




def t6_529root : Job := ⟨plan6538,[],none,⟨15,3,0⟩⟩
def t6_529jobs0 : List Job := [⟨plan6538,[],none,⟨15,3,0⟩⟩]

def t6_529jobs : List Job := t6_529jobs0




def t6_530root : Job := ⟨plan6539,[],none,⟨15,3,0⟩⟩
def t6_530jobs0 : List Job := [⟨plan6539,[],none,⟨15,3,0⟩⟩]

def t6_530jobs : List Job := t6_530jobs0




def t6_531root : Job := ⟨plan6540,[],none,⟨15,3,0⟩⟩
def t6_531jobs0 : List Job := [⟨plan6540,[],none,⟨15,3,0⟩⟩]

def t6_531jobs : List Job := t6_531jobs0




def t6_532root : Job := ⟨plan6541,[],none,⟨15,3,0⟩⟩
def t6_532jobs0 : List Job := [⟨plan6541,[],none,⟨15,3,0⟩⟩]

def t6_532jobs : List Job := t6_532jobs0




def t6_533root : Job := ⟨plan6542,[],none,⟨15,3,0⟩⟩
def t6_533jobs0 : List Job := [⟨plan6542,[],none,⟨15,3,0⟩⟩]

def t6_533jobs : List Job := t6_533jobs0




def t6_534root : Job := ⟨plan6543,[],none,⟨15,3,0⟩⟩
def t6_534jobs0 : List Job := [⟨plan6543,[],none,⟨15,3,0⟩⟩]

def t6_534jobs : List Job := t6_534jobs0




def t6_535root : Job := ⟨plan6544,[],none,⟨15,3,0⟩⟩
def t6_535jobs0 : List Job := [⟨plan6544,[],none,⟨15,3,0⟩⟩]

def t6_535jobs : List Job := t6_535jobs0




def t6_536root : Job := ⟨plan6545,[],none,⟨15,3,0⟩⟩
def t6_536jobs0 : List Job := [⟨plan6545,[],none,⟨15,3,0⟩⟩]

def t6_536jobs : List Job := t6_536jobs0




def t6_537root : Job := ⟨plan6373,[],none,⟨15,1,0⟩⟩
def t6_537jobs0 : List Job := [⟨plan6373,[],none,⟨15,1,0⟩⟩]

def t6_537jobs : List Job := t6_537jobs0




def t6_538root : Job := ⟨plan6546,[],none,⟨15,3,0⟩⟩
def t6_538jobs0 : List Job := [⟨plan6546,[],none,⟨15,3,0⟩⟩]

def t6_538jobs : List Job := t6_538jobs0




def t6_539root : Job := ⟨plan6547,[],none,⟨15,3,0⟩⟩
def t6_539jobs0 : List Job := [⟨plan6547,[],none,⟨15,3,0⟩⟩]

def t6_539jobs : List Job := t6_539jobs0




def t6_540root : Job := ⟨plan6548,[],none,⟨15,3,0⟩⟩
def t6_540jobs0 : List Job := [⟨plan6548,[],none,⟨15,3,0⟩⟩]

def t6_540jobs : List Job := t6_540jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


