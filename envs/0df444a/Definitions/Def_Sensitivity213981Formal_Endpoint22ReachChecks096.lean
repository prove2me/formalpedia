-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks096
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks096
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:32.071347+00:00
-- url     : https://prove2.me/theorems/9aab020c-5abc-4978-b28b-d9799389a1a7
-- title:
--   Endpoint22 Reach Checks096 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks096 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_799root`, `ThreeBoundEndpoint22Reachable.t6_799jobs0`, `ThreeBoundEndpoint22Reachable.t6_799jobs1`, `ThreeBoundEndpoint22Reachable.t6_799jobs`, `ThreeBoundEndpoint22Reachable.t6_800root`, `ThreeBoundEndpoint22Reachable.t6_800jobs0`, `ThreeBoundEndpoint22Reachable.t6_800jobs`, `ThreeBoundEndpoint22Reachable.t6_801root`, `ThreeBoundEndpoint22Reachable.t6_801jobs0`, `ThreeBoundEndpoint22Reachable.t6_801jobs`, `ThreeBoundEndpoint22Reachable.t6_802root`, `ThreeBoundEndpoint22Reachable.t6_802jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks096.lean, lines 1–190.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

def t6_793root : Job := ⟨plan7384,[],none,⟨15,10,0⟩⟩
def t6_793jobs0 : List Job := [⟨plan3479,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_793jobs1 : List Job := [⟨plan3479,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_793jobs : List Job := t6_793jobs0++t6_793jobs1




def t6_794root : Job := ⟨plan7385,[],none,⟨15,10,0⟩⟩
def t6_794jobs0 : List Job := [⟨plan7385,[],none,⟨15,10,0⟩⟩]

def t6_794jobs : List Job := t6_794jobs0




def t6_795root : Job := ⟨plan7386,[],none,⟨15,10,0⟩⟩
def t6_795jobs0 : List Job := [⟨plan3481,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_795jobs1 : List Job := [⟨plan3481,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_795jobs2 : List Job := [⟨plan3481,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_795jobs : List Job := t6_795jobs0++t6_795jobs1++t6_795jobs2




def t6_796root : Job := ⟨plan7387,[],none,⟨15,10,0⟩⟩
def t6_796jobs0 : List Job := [⟨plan3482,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_796jobs1 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_796jobs2 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_796jobs3 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_796jobs : List Job := t6_796jobs0++t6_796jobs1++t6_796jobs2++t6_796jobs3




def t6_797root : Job := ⟨plan7388,[],none,⟨15,10,0⟩⟩
def t6_797jobs0 : List Job := [⟨plan3483,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_797jobs1 : List Job := [⟨plan3483,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_797jobs : List Job := t6_797jobs0++t6_797jobs1




def t6_798root : Job := ⟨plan7389,[],none,⟨15,10,0⟩⟩
def t6_798jobs0 : List Job := [⟨plan7389,[],none,⟨15,10,0⟩⟩]

def t6_798jobs : List Job := t6_798jobs0




def t6_799root : Job := ⟨plan7390,[],none,⟨15,10,0⟩⟩
def t6_799jobs0 : List Job := [⟨plan5947,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5947,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_799jobs1 : List Job := [⟨plan5947,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_799jobs : List Job := t6_799jobs0++t6_799jobs1




def t6_800root : Job := ⟨plan6400,[],none,⟨15,1,0⟩⟩
def t6_800jobs0 : List Job := [⟨plan6400,[],none,⟨15,1,0⟩⟩]

def t6_800jobs : List Job := t6_800jobs0




def t6_801root : Job := ⟨plan6605,[],none,⟨15,3,0⟩⟩
def t6_801jobs0 : List Job := [⟨plan6605,[],none,⟨15,3,0⟩⟩]

def t6_801jobs : List Job := t6_801jobs0




def t6_802root : Job := ⟨plan6606,[],none,⟨15,3,0⟩⟩
def t6_802jobs0 : List Job := [⟨plan5534,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5534,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5534,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5534,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩,⟨plan5534,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_802jobs1 : List Job := [⟨plan5534,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_802jobs : List Job := t6_802jobs0++t6_802jobs1




def t6_803root : Job := ⟨plan6607,[],none,⟨15,3,0⟩⟩
def t6_803jobs0 : List Job := [⟨plan6607,[],none,⟨15,3,0⟩⟩]

def t6_803jobs : List Job := t6_803jobs0




def t6_804root : Job := ⟨plan6964,[],none,⟨15,6,0⟩⟩
def t6_804jobs0 : List Job := [⟨plan6964,[],none,⟨15,6,0⟩⟩]

def t6_804jobs : List Job := t6_804jobs0




def t6_805root : Job := ⟨plan6965,[],none,⟨15,6,0⟩⟩
def t6_805jobs0 : List Job := [⟨plan5734,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5734,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5734,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_805jobs1 : List Job := [⟨plan5734,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_805jobs2 : List Job := [⟨plan5734,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_805jobs : List Job := t6_805jobs0++t6_805jobs1++t6_805jobs2




def t6_806root : Job := ⟨plan6966,[],none,⟨15,6,0⟩⟩
def t6_806jobs0 : List Job := [⟨plan6966,[],none,⟨15,6,0⟩⟩]

def t6_806jobs : List Job := t6_806jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


