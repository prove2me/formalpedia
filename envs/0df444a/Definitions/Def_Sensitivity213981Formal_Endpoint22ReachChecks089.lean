-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks089
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks089
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:28.602153+00:00
-- url     : https://prove2.me/theorems/9d7f6803-d2ac-4c4e-b859-653dc08640ea
-- title:
--   Endpoint22 Reach Checks089 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks089 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_757jobs1`, `ThreeBoundEndpoint22Reachable.t6_757jobs`, `ThreeBoundEndpoint22Reachable.t6_758root`, `ThreeBoundEndpoint22Reachable.t6_758jobs0`, `ThreeBoundEndpoint22Reachable.t6_758jobs`, `ThreeBoundEndpoint22Reachable.t6_759root`, `ThreeBoundEndpoint22Reachable.t6_759jobs0`, `ThreeBoundEndpoint22Reachable.t6_759jobs1`, `ThreeBoundEndpoint22Reachable.t6_759jobs2`, `ThreeBoundEndpoint22Reachable.t6_759jobs`, `ThreeBoundEndpoint22Reachable.t6_749jobs1`, `ThreeBoundEndpoint22Reachable.t6_760root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks089.lean, lines 1–163.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_749root : Job := ⟨plan7360,[],none,⟨15,10,0⟩⟩
def t6_749jobs0 : List Job := [⟨plan3507,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_749jobs1 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_749jobs2 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_749jobs : List Job := t6_749jobs0++t6_749jobs1++t6_749jobs2




def t6_750root : Job := ⟨plan7361,[],none,⟨15,10,0⟩⟩
def t6_750jobs0 : List Job := [⟨plan3508,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_750jobs1 : List Job := [⟨plan3508,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_750jobs : List Job := t6_750jobs0++t6_750jobs1




def t6_751root : Job := ⟨plan7362,[],none,⟨15,10,0⟩⟩
def t6_751jobs0 : List Job := [⟨plan7362,[],none,⟨15,10,0⟩⟩]

def t6_751jobs : List Job := t6_751jobs0




def t6_752root : Job := ⟨plan7363,[],none,⟨15,10,0⟩⟩
def t6_752jobs0 : List Job := [⟨plan7363,[],none,⟨15,10,0⟩⟩]

def t6_752jobs : List Job := t6_752jobs0




def t6_753root : Job := ⟨plan7364,[],none,⟨15,10,0⟩⟩
def t6_753jobs0 : List Job := [⟨plan7364,[],none,⟨15,10,0⟩⟩]

def t6_753jobs : List Job := t6_753jobs0




def t6_754root : Job := ⟨plan7365,[],none,⟨15,10,0⟩⟩
def t6_754jobs0 : List Job := [⟨plan7365,[],none,⟨15,10,0⟩⟩]

def t6_754jobs : List Job := t6_754jobs0




def t6_755root : Job := ⟨plan7366,[],none,⟨15,10,0⟩⟩
def t6_755jobs0 : List Job := [⟨plan7366,[],none,⟨15,10,0⟩⟩]

def t6_755jobs : List Job := t6_755jobs0




def t6_756root : Job := ⟨plan7367,[],none,⟨15,10,0⟩⟩
def t6_756jobs0 : List Job := [⟨plan5886,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5886,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_756jobs1 : List Job := [⟨plan5886,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_756jobs : List Job := t6_756jobs0++t6_756jobs1




def t6_757root : Job := ⟨plan7368,[],none,⟨15,10,0⟩⟩
def t6_757jobs0 : List Job := [⟨plan3479,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_757jobs1 : List Job := [⟨plan3479,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_757jobs : List Job := t6_757jobs0++t6_757jobs1




def t6_758root : Job := ⟨plan7369,[],none,⟨15,10,0⟩⟩
def t6_758jobs0 : List Job := [⟨plan7369,[],none,⟨15,10,0⟩⟩]

def t6_758jobs : List Job := t6_758jobs0




def t6_759root : Job := ⟨plan7370,[],none,⟨15,10,0⟩⟩
def t6_759jobs0 : List Job := [⟨plan3481,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_759jobs1 : List Job := [⟨plan3481,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_759jobs2 : List Job := [⟨plan3481,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_759jobs : List Job := t6_759jobs0++t6_759jobs1++t6_759jobs2




def t6_760root : Job := ⟨plan7371,[],none,⟨15,10,0⟩⟩
def t6_760jobs0 : List Job := [⟨plan3482,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩]

def t6_760jobs1 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_760jobs2 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_760jobs3 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_760jobs : List Job := t6_760jobs0++t6_760jobs1++t6_760jobs2++t6_760jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


