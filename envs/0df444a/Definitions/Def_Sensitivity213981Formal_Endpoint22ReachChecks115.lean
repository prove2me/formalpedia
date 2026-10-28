-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks115
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks115
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:04.748775+00:00
-- url     : https://prove2.me/theorems/6f54e44d-1a01-4aa8-ac61-bd3a4eb455d3
-- title:
--   Endpoint22 Reach Checks115 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks115 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_886jobs3`, `ThreeBoundEndpoint22Reachable.t6_886jobs`, `ThreeBoundEndpoint22Reachable.t6_887root`, `ThreeBoundEndpoint22Reachable.t6_887jobs0`, `ThreeBoundEndpoint22Reachable.t6_887jobs1`, `ThreeBoundEndpoint22Reachable.t6_887jobs`, `ThreeBoundEndpoint22Reachable.t6_888root`, `ThreeBoundEndpoint22Reachable.t6_888jobs0`, `ThreeBoundEndpoint22Reachable.t6_888jobs`, `ThreeBoundEndpoint22Reachable.t6_889root`, `ThreeBoundEndpoint22Reachable.t6_889jobs0`, `ThreeBoundEndpoint22Reachable.t6_889jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks115.lean, lines 1–196.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

def t6_884root : Job := ⟨plan7429,[],none,⟨15,10,0⟩⟩
def t6_884jobs0 : List Job := [⟨plan3485,[⟨3,0,5⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_884jobs1 : List Job := [⟨plan3485,[⟨3,2,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_884jobs2 : List Job := [⟨plan3485,[⟨3,2,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨12,6,(-6)⟩⟩]

def t6_884jobs3 : List Job := [⟨plan3485,[⟨3,3,2⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨11,6,(-5)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨10,8,(-2)⟩⟩]

def t6_884jobs4 : List Job := [⟨plan3485,[⟨3,3,2⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨10,7,(-3)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨9,9,0⟩⟩]

def t6_884jobs5 : List Job := [⟨plan3485,[⟨3,3,2⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_884jobs : List Job := t6_884jobs0++t6_884jobs1++t6_884jobs2++t6_884jobs3++t6_884jobs4++t6_884jobs5




def t6_885root : Job := ⟨plan7430,[],none,⟨15,10,0⟩⟩
def t6_885jobs0 : List Job := [⟨plan3507,[⟨3,0,5⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_885jobs1 : List Job := [⟨plan3507,[⟨3,2,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_885jobs2 : List Job := [⟨plan3507,[⟨3,2,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3507,[⟨3,3,2⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨12,6,(-6)⟩⟩]

def t6_885jobs3 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3507,[⟨3,3,2⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨11,6,(-5)⟩⟩]

def t6_885jobs4 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3507,[⟨3,3,2⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨10,7,(-3)⟩⟩]

def t6_885jobs5 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨9,9,0⟩⟩,⟨plan3507,[⟨3,3,2⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_885jobs : List Job := t6_885jobs0++t6_885jobs1++t6_885jobs2++t6_885jobs3++t6_885jobs4++t6_885jobs5




def t6_886root : Job := ⟨plan7431,[],none,⟨15,10,0⟩⟩
def t6_886jobs0 : List Job := [⟨plan3508,[⟨3,0,5⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_886jobs1 : List Job := [⟨plan3508,[⟨3,2,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨12,6,(-6)⟩⟩]

def t6_886jobs2 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨11,6,(-5)⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨10,8,(-2)⟩⟩]

def t6_886jobs3 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨10,7,(-3)⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨9,9,0⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_886jobs : List Job := t6_886jobs0++t6_886jobs1++t6_886jobs2++t6_886jobs3




def t6_887root : Job := ⟨plan7432,[],none,⟨15,10,0⟩⟩
def t6_887jobs0 : List Job := [⟨plan5975,[⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5975,[⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,10,(-4)⟩⟩,⟨plan5975,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_887jobs1 : List Job := [⟨plan5975,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,10,(-2)⟩⟩]

def t6_887jobs : List Job := t6_887jobs0++t6_887jobs1




def t6_888root : Job := ⟨plan7433,[],none,⟨15,10,0⟩⟩
def t6_888jobs0 : List Job := [⟨plan7433,[],none,⟨15,10,0⟩⟩]

def t6_888jobs : List Job := t6_888jobs0




def t6_889root : Job := ⟨plan6618,[],none,⟨15,3,0⟩⟩
def t6_889jobs0 : List Job := [⟨plan6618,[],none,⟨15,3,0⟩⟩]

def t6_889jobs : List Job := t6_889jobs0




def t6_890root : Job := ⟨plan6407,[],none,⟨15,1,0⟩⟩
def t6_890jobs0 : List Job := [⟨plan6407,[],none,⟨15,1,0⟩⟩]

def t6_890jobs : List Job := t6_890jobs0




def t6_891root : Job := ⟨plan6619,[],none,⟨15,3,0⟩⟩
def t6_891jobs0 : List Job := [⟨plan6619,[],none,⟨15,3,0⟩⟩]

def t6_891jobs : List Job := t6_891jobs0




def t6_892root : Job := ⟨plan6620,[],none,⟨15,3,0⟩⟩
def t6_892jobs0 : List Job := [⟨plan6620,[],none,⟨15,3,0⟩⟩]

def t6_892jobs : List Job := t6_892jobs0




def t6_893root : Job := ⟨plan6621,[],none,⟨15,3,0⟩⟩
def t6_893jobs0 : List Job := [⟨plan6621,[],none,⟨15,3,0⟩⟩]

def t6_893jobs : List Job := t6_893jobs0




def t6_894root : Job := ⟨plan6986,[],none,⟨15,6,0⟩⟩
def t6_894jobs0 : List Job := [⟨plan6986,[],none,⟨15,6,0⟩⟩]

def t6_894jobs : List Job := t6_894jobs0




def t6_895root : Job := ⟨plan6987,[],none,⟨15,6,0⟩⟩
def t6_895jobs0 : List Job := [⟨plan6987,[],none,⟨15,6,0⟩⟩]

def t6_895jobs : List Job := t6_895jobs0




def t6_896root : Job := ⟨plan6988,[],none,⟨15,6,0⟩⟩
def t6_896jobs0 : List Job := [⟨plan6988,[],none,⟨15,6,0⟩⟩]

def t6_896jobs : List Job := t6_896jobs0




def t6_897root : Job := ⟨plan6989,[],none,⟨15,6,0⟩⟩
def t6_897jobs0 : List Job := [⟨plan6989,[],none,⟨15,6,0⟩⟩]

def t6_897jobs : List Job := t6_897jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


