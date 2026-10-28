-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks098
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks098
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:45.959159+00:00
-- url     : https://prove2.me/theorems/14cad0c8-c90a-439c-83ba-c008761c95d0
-- title:
--   Endpoint22 Reach Checks098 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks098 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_838jobs`, `ThreeBoundEndpoint22Reachable.t6_839root`, `ThreeBoundEndpoint22Reachable.t6_839jobs0`, `ThreeBoundEndpoint22Reachable.t6_839jobs1`, `ThreeBoundEndpoint22Reachable.t6_839jobs`, `ThreeBoundEndpoint22Reachable.t6_840root`, `ThreeBoundEndpoint22Reachable.t6_840jobs0`, `ThreeBoundEndpoint22Reachable.t6_840jobs1`, `ThreeBoundEndpoint22Reachable.t6_840jobs2`, `ThreeBoundEndpoint22Reachable.t6_840jobs`, `ThreeBoundEndpoint22Reachable.t6_841root`, `ThreeBoundEndpoint22Reachable.t6_841jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks098.lean, lines 1–191.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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

def t6_829root : Job := ⟨plan7409,[],none,⟨15,10,0⟩⟩
def t6_829jobs0 : List Job := [⟨plan3507,[⟨2,0,5⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_829jobs1 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_829jobs2 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_829jobs : List Job := t6_829jobs0++t6_829jobs1++t6_829jobs2




def t6_830root : Job := ⟨plan7410,[],none,⟨15,10,0⟩⟩
def t6_830jobs0 : List Job := [⟨plan5974,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5974,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_830jobs1 : List Job := [⟨plan5974,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_830jobs : List Job := t6_830jobs0++t6_830jobs1




def t6_831root : Job := ⟨plan7411,[],none,⟨15,10,0⟩⟩
def t6_831jobs0 : List Job := [⟨plan7411,[],none,⟨15,10,0⟩⟩]

def t6_831jobs : List Job := t6_831jobs0




def t6_832root : Job := ⟨plan7412,[],none,⟨15,10,0⟩⟩
def t6_832jobs0 : List Job := [⟨plan7412,[],none,⟨15,10,0⟩⟩]

def t6_832jobs : List Job := t6_832jobs0




def t6_833root : Job := ⟨plan6282,[],none,⟨15,0,0⟩⟩
def t6_833jobs0 : List Job := [⟨plan6282,[],none,⟨15,0,0⟩⟩]

def t6_833jobs : List Job := t6_833jobs0




def t6_834root : Job := ⟨plan6311,[],none,⟨15,0,0⟩⟩
def t6_834jobs0 : List Job := [⟨plan6311,[],none,⟨15,0,0⟩⟩]

def t6_834jobs : List Job := t6_834jobs0




def t6_835root : Job := ⟨plan6312,[],none,⟨15,0,0⟩⟩
def t6_835jobs0 : List Job := [⟨plan6312,[],none,⟨15,0,0⟩⟩]

def t6_835jobs : List Job := t6_835jobs0




def t6_836root : Job := ⟨plan6313,[],none,⟨15,0,0⟩⟩
def t6_836jobs0 : List Job := [⟨plan6313,[],none,⟨15,0,0⟩⟩]

def t6_836jobs : List Job := t6_836jobs0




def t6_837root : Job := ⟨plan6401,[],none,⟨15,1,0⟩⟩
def t6_837jobs0 : List Job := [⟨plan6401,[],none,⟨15,1,0⟩⟩]

def t6_837jobs : List Job := t6_837jobs0




def t6_838root : Job := ⟨plan6402,[],none,⟨15,1,0⟩⟩
def t6_838jobs0 : List Job := [⟨plan5397,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5397,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_838jobs1 : List Job := [⟨plan5397,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_838jobs2 : List Job := [⟨plan5397,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨13,1,0⟩⟩]

def t6_838jobs3 : List Job := [⟨plan5397,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5397,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-2)⟩⟩,⟨plan5397,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,0⟩⟩,⟨plan5397,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-1)⟩⟩,⟨plan5397,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-2)⟩⟩]

def t6_838jobs : List Job := t6_838jobs0++t6_838jobs1++t6_838jobs2++t6_838jobs3




def t6_839root : Job := ⟨plan6403,[],none,⟨15,1,0⟩⟩
def t6_839jobs0 : List Job := [⟨plan5398,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5398,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨14,1,(-1)⟩⟩,⟨plan5398,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-2)⟩⟩,⟨plan5398,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨13,1,0⟩⟩]

def t6_839jobs1 : List Job := [⟨plan5398,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5398,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-2)⟩⟩,⟨plan5398,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,0⟩⟩,⟨plan5398,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-1)⟩⟩,⟨plan5398,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-2)⟩⟩]

def t6_839jobs : List Job := t6_839jobs0++t6_839jobs1




def t6_840root : Job := ⟨plan6404,[],none,⟨15,1,0⟩⟩
def t6_840jobs0 : List Job := [⟨plan5399,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5399,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_840jobs1 : List Job := [⟨plan5399,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-2)⟩⟩,⟨plan5399,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨13,1,0⟩⟩]

def t6_840jobs2 : List Job := [⟨plan5399,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5399,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-2)⟩⟩,⟨plan5399,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,0⟩⟩,⟨plan5399,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-1)⟩⟩,⟨plan5399,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-2)⟩⟩]

def t6_840jobs : List Job := t6_840jobs0++t6_840jobs1++t6_840jobs2




def t6_841root : Job := ⟨plan6405,[],none,⟨15,1,0⟩⟩
def t6_841jobs0 : List Job := [⟨plan5400,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5400,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_841jobs1 : List Job := [⟨plan5400,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_841jobs2 : List Job := [⟨plan5400,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨13,1,0⟩⟩]

def t6_841jobs3 : List Job := [⟨plan5400,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5400,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-2)⟩⟩,⟨plan5400,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,0⟩⟩,⟨plan5400,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-1)⟩⟩,⟨plan5400,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-2)⟩⟩]

def t6_841jobs : List Job := t6_841jobs0++t6_841jobs1++t6_841jobs2++t6_841jobs3




def t6_842root : Job := ⟨plan6406,[],none,⟨15,1,0⟩⟩
def t6_842jobs0 : List Job := [⟨plan6406,[],none,⟨15,1,0⟩⟩]

def t6_842jobs : List Job := t6_842jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


