-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks088
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks088
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:23.117746+00:00
-- url     : https://prove2.me/theorems/0139c2c2-2b2e-475d-8b73-56b441c79cf2
-- title:
--   Endpoint22 Reach Checks088 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks088 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_737jobs`, `ThreeBoundEndpoint22Reachable.t6_738root`, `ThreeBoundEndpoint22Reachable.t6_738jobs0`, `ThreeBoundEndpoint22Reachable.t6_738jobs1`, `ThreeBoundEndpoint22Reachable.t6_732root`, `ThreeBoundEndpoint22Reachable.t6_738jobs`, `ThreeBoundEndpoint22Reachable.t6_732jobs0`, `ThreeBoundEndpoint22Reachable.t6_739root`, `ThreeBoundEndpoint22Reachable.t6_739jobs0`, `ThreeBoundEndpoint22Reachable.t6_739jobs`, `ThreeBoundEndpoint22Reachable.t6_740root`, `ThreeBoundEndpoint22Reachable.t6_740jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks088.lean, lines 1–230.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_731root : Job := ⟨plan6949,[],none,⟨15,6,0⟩⟩
def t6_731jobs0 : List Job := [⟨plan6949,[],none,⟨15,6,0⟩⟩]

def t6_731jobs : List Job := t6_731jobs0




def t6_732root : Job := ⟨plan6950,[],none,⟨15,6,0⟩⟩
def t6_732jobs0 : List Job := [⟨plan3416,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3416,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3416,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3416,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3416,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3416,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3416,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3416,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3416,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3416,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3416,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3416,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3416,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3416,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3416,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3416,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_732jobs1 : List Job := [⟨plan3416,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3416,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3416,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3416,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3416,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3416,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩]

def t6_732jobs2 : List Job := [⟨plan3416,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩,⟨plan3416,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3416,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3416,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩]

def t6_732jobs3 : List Job := [⟨plan3416,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3416,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩,⟨plan3416,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_732jobs4 : List Job := [⟨plan3416,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_732jobs : List Job := t6_732jobs0++t6_732jobs1++t6_732jobs2++t6_732jobs3++t6_732jobs4




def t6_733root : Job := ⟨plan6951,[],none,⟨15,6,0⟩⟩
def t6_733jobs0 : List Job := [⟨plan3417,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3417,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3417,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3417,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3417,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3417,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3417,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3417,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3417,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3417,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3417,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3417,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3417,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3417,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3417,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_733jobs1 : List Job := [⟨plan3417,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩,⟨plan3417,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩,⟨plan3417,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3417,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩]

def t6_733jobs2 : List Job := [⟨plan3417,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3417,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3417,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩,⟨plan3417,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_733jobs3 : List Job := [⟨plan3417,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_733jobs : List Job := t6_733jobs0++t6_733jobs1++t6_733jobs2++t6_733jobs3




def t6_734root : Job := ⟨plan6952,[],none,⟨15,6,0⟩⟩
def t6_734jobs0 : List Job := [⟨plan6952,[],none,⟨15,6,0⟩⟩]

def t6_734jobs : List Job := t6_734jobs0




def t6_735root : Job := ⟨plan7347,[],none,⟨15,10,0⟩⟩
def t6_735jobs0 : List Job := [⟨plan7347,[],none,⟨15,10,0⟩⟩]

def t6_735jobs : List Job := t6_735jobs0




def t6_736root : Job := ⟨plan7348,[],none,⟨15,10,0⟩⟩
def t6_736jobs0 : List Job := [⟨plan7348,[],none,⟨15,10,0⟩⟩]

def t6_736jobs : List Job := t6_736jobs0




def t6_737root : Job := ⟨plan7349,[],none,⟨15,10,0⟩⟩
def t6_737jobs0 : List Job := [⟨plan7349,[],none,⟨15,10,0⟩⟩]

def t6_737jobs : List Job := t6_737jobs0




def t6_738root : Job := ⟨plan7350,[],none,⟨15,10,0⟩⟩
def t6_738jobs0 : List Job := [⟨plan3496,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3496,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3496,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3496,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3496,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3496,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3496,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3496,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3496,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3496,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3496,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3496,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3496,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3496,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_738jobs1 : List Job := [⟨plan3496,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_738jobs : List Job := t6_738jobs0++t6_738jobs1




def t6_739root : Job := ⟨plan7351,[],none,⟨15,10,0⟩⟩
def t6_739jobs0 : List Job := [⟨plan7351,[],none,⟨15,10,0⟩⟩]

def t6_739jobs : List Job := t6_739jobs0




def t6_740root : Job := ⟨plan7352,[],none,⟨15,10,0⟩⟩
def t6_740jobs0 : List Job := [⟨plan7352,[],none,⟨15,10,0⟩⟩]

def t6_740jobs : List Job := t6_740jobs0




def t6_741root : Job := ⟨plan7353,[],none,⟨15,10,0⟩⟩
def t6_741jobs0 : List Job := [⟨plan5871,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5871,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_741jobs1 : List Job := [⟨plan5871,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_741jobs : List Job := t6_741jobs0++t6_741jobs1




def t6_742root : Job := ⟨plan6953,[],none,⟨15,6,0⟩⟩
def t6_742jobs0 : List Job := [⟨plan6953,[],none,⟨15,6,0⟩⟩]

def t6_742jobs : List Job := t6_742jobs0




def t6_743root : Job := ⟨plan7354,[],none,⟨15,10,0⟩⟩
def t6_743jobs0 : List Job := [⟨plan7354,[],none,⟨15,10,0⟩⟩]

def t6_743jobs : List Job := t6_743jobs0




def t6_744root : Job := ⟨plan7355,[],none,⟨15,10,0⟩⟩
def t6_744jobs0 : List Job := [⟨plan7355,[],none,⟨15,10,0⟩⟩]

def t6_744jobs : List Job := t6_744jobs0




def t6_745root : Job := ⟨plan7356,[],none,⟨15,10,0⟩⟩
def t6_745jobs0 : List Job := [⟨plan7356,[],none,⟨15,10,0⟩⟩]

def t6_745jobs : List Job := t6_745jobs0




def t6_746root : Job := ⟨plan7357,[],none,⟨15,10,0⟩⟩
def t6_746jobs0 : List Job := [⟨plan3504,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3504,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3504,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3504,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3504,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3504,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3504,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3504,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3504,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3504,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3504,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3504,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3504,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3504,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_746jobs1 : List Job := [⟨plan3504,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_746jobs : List Job := t6_746jobs0++t6_746jobs1




def t6_747root : Job := ⟨plan7358,[],none,⟨15,10,0⟩⟩
def t6_747jobs0 : List Job := [⟨plan7358,[],none,⟨15,10,0⟩⟩]

def t6_747jobs : List Job := t6_747jobs0




def t6_748root : Job := ⟨plan7359,[],none,⟨15,10,0⟩⟩
def t6_748jobs0 : List Job := [⟨plan7359,[],none,⟨15,10,0⟩⟩]

def t6_748jobs : List Job := t6_748jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


