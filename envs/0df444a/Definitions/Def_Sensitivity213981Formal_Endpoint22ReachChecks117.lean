-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks117
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks117
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:37.052459+00:00
-- url     : https://prove2.me/theorems/0a350ea8-7645-4dd3-bbdd-5d23cf97d318
-- title:
--   Endpoint22 Reach Checks117 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks117 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_929jobs`, `ThreeBoundEndpoint22Reachable.t6_930root`, `ThreeBoundEndpoint22Reachable.t6_930jobs0`, `ThreeBoundEndpoint22Reachable.t6_930jobs`, `ThreeBoundEndpoint22Reachable.t6_931root`, `ThreeBoundEndpoint22Reachable.t6_931jobs0`, `ThreeBoundEndpoint22Reachable.t6_931jobs`, `ThreeBoundEndpoint22Reachable.t6_932root`, `ThreeBoundEndpoint22Reachable.t6_932jobs0`, `ThreeBoundEndpoint22Reachable.t6_932jobs`, `ThreeBoundEndpoint22Reachable.t6_933root`, `ThreeBoundEndpoint22Reachable.t6_933jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks117.lean, lines 1–389.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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

def t6_919root : Job := ⟨plan7001,[],none,⟨15,6,0⟩⟩
def t6_919jobs0 : List Job := [⟨plan3367,[⟨4,0,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_919jobs1 : List Job := [⟨plan3367,[⟨4,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_919jobs2 : List Job := [⟨plan3367,[⟨4,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_919jobs : List Job := t6_919jobs0++t6_919jobs1++t6_919jobs2




def t6_920root : Job := ⟨plan7002,[],none,⟨15,6,0⟩⟩
def t6_920jobs0 : List Job := [⟨plan5570,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5570,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_920jobs1 : List Job := [⟨plan5570,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_920jobs : List Job := t6_920jobs0++t6_920jobs1




def t6_921root : Job := ⟨plan7003,[],none,⟨15,6,0⟩⟩
def t6_921jobs0 : List Job := [⟨plan7003,[],none,⟨15,6,0⟩⟩]

def t6_921jobs : List Job := t6_921jobs0




def t6_922root : Job := ⟨plan6628,[],none,⟨15,3,0⟩⟩
def t6_922jobs0 : List Job := [⟨plan6628,[],none,⟨15,3,0⟩⟩]

def t6_922jobs : List Job := t6_922jobs0




def t6_923root : Job := ⟨plan7004,[],none,⟨15,6,0⟩⟩
def t6_923jobs0 : List Job := [⟨plan7004,[],none,⟨15,6,0⟩⟩]

def t6_923jobs : List Job := t6_923jobs0




def t6_924root : Job := ⟨plan7005,[],none,⟨15,6,0⟩⟩
def t6_924jobs0 : List Job := [⟨plan5573,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5573,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_924jobs1 : List Job := [⟨plan5573,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_924jobs : List Job := t6_924jobs0++t6_924jobs1




def t6_925root : Job := ⟨plan7006,[],none,⟨15,6,0⟩⟩
def t6_925jobs0 : List Job := [⟨plan7006,[],none,⟨15,6,0⟩⟩]

def t6_925jobs : List Job := t6_925jobs0




def t6_926root : Job := ⟨plan7434,[],none,⟨15,10,0⟩⟩
def t6_926jobs0 : List Job := [⟨plan7434,[],none,⟨15,10,0⟩⟩]

def t6_926jobs : List Job := t6_926jobs0




def t6_927root : Job := ⟨plan7435,[],none,⟨15,10,0⟩⟩
def t6_927jobs0 : List Job := [⟨plan7435,[],none,⟨15,10,0⟩⟩]

def t6_927jobs : List Job := t6_927jobs0




def t6_928root : Job := ⟨plan7436,[],none,⟨15,10,0⟩⟩
def t6_928jobs0 : List Job := [⟨plan7436,[],none,⟨15,10,0⟩⟩]

def t6_928jobs : List Job := t6_928jobs0




def t6_929root : Job := ⟨plan7437,[],none,⟨15,10,0⟩⟩
def t6_929jobs0 : List Job := [⟨plan7437,[],none,⟨15,10,0⟩⟩]

def t6_929jobs : List Job := t6_929jobs0




def t6_930root : Job := ⟨plan7438,[],none,⟨15,10,0⟩⟩
def t6_930jobs0 : List Job := [⟨plan7438,[],none,⟨15,10,0⟩⟩]

def t6_930jobs : List Job := t6_930jobs0




def t6_931root : Job := ⟨plan7439,[],none,⟨15,10,0⟩⟩
def t6_931jobs0 : List Job := [⟨plan7439,[],none,⟨15,10,0⟩⟩]

def t6_931jobs : List Job := t6_931jobs0




def t6_932root : Job := ⟨plan7440,[],none,⟨15,10,0⟩⟩
def t6_932jobs0 : List Job := [⟨plan7440,[],none,⟨15,10,0⟩⟩]

def t6_932jobs : List Job := t6_932jobs0




def t6_933root : Job := ⟨plan7441,[],none,⟨15,10,0⟩⟩
def t6_933jobs0 : List Job := [⟨plan7441,[],none,⟨15,10,0⟩⟩]

def t6_933jobs : List Job := t6_933jobs0




def t6_934root : Job := ⟨plan7442,[],none,⟨15,10,0⟩⟩
def t6_934jobs0 : List Job := [⟨plan7442,[],none,⟨15,10,0⟩⟩]

def t6_934jobs : List Job := t6_934jobs0




def t6_935root : Job := ⟨plan7443,[],none,⟨15,10,0⟩⟩
def t6_935jobs0 : List Job := [⟨plan7443,[],none,⟨15,10,0⟩⟩]

def t6_935jobs : List Job := t6_935jobs0




def t6_936root : Job := ⟨plan7444,[],none,⟨15,10,0⟩⟩
def t6_936jobs0 : List Job := [⟨plan7444,[],none,⟨15,10,0⟩⟩]

def t6_936jobs : List Job := t6_936jobs0




def t6_937root : Job := ⟨plan7445,[],none,⟨15,10,0⟩⟩
def t6_937jobs0 : List Job := [⟨plan7445,[],none,⟨15,10,0⟩⟩]

def t6_937jobs : List Job := t6_937jobs0




def t6_938root : Job := ⟨plan7446,[],none,⟨15,10,0⟩⟩
def t6_938jobs0 : List Job := [⟨plan7446,[],none,⟨15,10,0⟩⟩]

def t6_938jobs : List Job := t6_938jobs0




def t6_939root : Job := ⟨plan7447,[],none,⟨15,10,0⟩⟩
def t6_939jobs0 : List Job := [⟨plan7447,[],none,⟨15,10,0⟩⟩]

def t6_939jobs : List Job := t6_939jobs0




def t6_940root : Job := ⟨plan7448,[],none,⟨15,10,0⟩⟩
def t6_940jobs0 : List Job := [⟨plan7448,[],none,⟨15,10,0⟩⟩]

def t6_940jobs : List Job := t6_940jobs0




def t6_941root : Job := ⟨plan7449,[],none,⟨15,10,0⟩⟩
def t6_941jobs0 : List Job := [⟨plan5755,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5755,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_941jobs1 : List Job := [⟨plan5755,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_941jobs : List Job := t6_941jobs0++t6_941jobs1




def t6_942root : Job := ⟨plan7450,[],none,⟨15,10,0⟩⟩
def t6_942jobs0 : List Job := [⟨plan7450,[],none,⟨15,10,0⟩⟩]

def t6_942jobs : List Job := t6_942jobs0




def t6_943root : Job := ⟨plan7451,[],none,⟨15,10,0⟩⟩
def t6_943jobs0 : List Job := [⟨plan7451,[],none,⟨15,10,0⟩⟩]

def t6_943jobs : List Job := t6_943jobs0




def t6_944root : Job := ⟨plan7452,[],none,⟨15,10,0⟩⟩
def t6_944jobs0 : List Job := [⟨plan7452,[],none,⟨15,10,0⟩⟩]

def t6_944jobs : List Job := t6_944jobs0




def t6_945root : Job := ⟨plan6629,[],none,⟨15,3,0⟩⟩
def t6_945jobs0 : List Job := [⟨plan6629,[],none,⟨15,3,0⟩⟩]

def t6_945jobs : List Job := t6_945jobs0




def t6_946root : Job := ⟨plan7007,[],none,⟨15,6,0⟩⟩
def t6_946jobs0 : List Job := [⟨plan7007,[],none,⟨15,6,0⟩⟩]

def t6_946jobs : List Job := t6_946jobs0




def t6_947root : Job := ⟨plan7008,[],none,⟨15,6,0⟩⟩
def t6_947jobs0 : List Job := [⟨plan5603,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5603,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_947jobs1 : List Job := [⟨plan5603,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_947jobs : List Job := t6_947jobs0++t6_947jobs1




def t6_948root : Job := ⟨plan7009,[],none,⟨15,6,0⟩⟩
def t6_948jobs0 : List Job := [⟨plan7009,[],none,⟨15,6,0⟩⟩]

def t6_948jobs : List Job := t6_948jobs0




def t6_949root : Job := ⟨plan7453,[],none,⟨15,10,0⟩⟩
def t6_949jobs0 : List Job := [⟨plan7453,[],none,⟨15,10,0⟩⟩]

def t6_949jobs : List Job := t6_949jobs0




def t6_950root : Job := ⟨plan7454,[],none,⟨15,10,0⟩⟩
def t6_950jobs0 : List Job := [⟨plan7454,[],none,⟨15,10,0⟩⟩]

def t6_950jobs : List Job := t6_950jobs0




def t6_951root : Job := ⟨plan7455,[],none,⟨15,10,0⟩⟩
def t6_951jobs0 : List Job := [⟨plan7455,[],none,⟨15,10,0⟩⟩]

def t6_951jobs : List Job := t6_951jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


