-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks183
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks183
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:34:07.957135+00:00
-- url     : https://prove2.me/theorems/61340be0-835e-49d0-990c-2014495b823b
-- title:
--   Endpoint22 Reach Checks183 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks183 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_339root`, `ThreeBoundEndpoint22Reachable.t7_339jobs0`, `ThreeBoundEndpoint22Reachable.t7_339jobs`, `ThreeBoundEndpoint22Reachable.t7_340root`, `ThreeBoundEndpoint22Reachable.t7_340jobs0`, `ThreeBoundEndpoint22Reachable.t7_340jobs`, `ThreeBoundEndpoint22Reachable.t7_341root`, `ThreeBoundEndpoint22Reachable.t7_341jobs0`, `ThreeBoundEndpoint22Reachable.t7_341jobs`, `ThreeBoundEndpoint22Reachable.t7_342root`, `ThreeBoundEndpoint22Reachable.t7_342jobs0`, `ThreeBoundEndpoint22Reachable.t7_342jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks183.lean, lines 1–324.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
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

def t7_336root : Job := ⟨plan8834,[],none,⟨21,15,0⟩⟩
def t7_336jobs0 : List Job := [⟨plan6225,[⟨3,0,6⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨17,11,(-6)⟩⟩]

def t7_336jobs1 : List Job := [⟨plan6225,[⟨3,2,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_336jobs2 : List Job := [⟨plan6225,[⟨3,3,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨16,11,(-5)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨15,13,(-2)⟩⟩]

def t7_336jobs3 : List Job := [⟨plan6225,[⟨3,3,3⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_336jobs : List Job := t7_336jobs0++t7_336jobs1++t7_336jobs2++t7_336jobs3




def t7_337root : Job := ⟨plan8835,[],none,⟨21,15,0⟩⟩
def t7_337jobs0 : List Job := [⟨plan6230,[⟨3,0,6⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨16,13,(-3)⟩⟩]

def t7_337jobs1 : List Job := [⟨plan6230,[⟨3,2,4⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_337jobs2 : List Job := [⟨plan6230,[⟨3,3,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨16,11,(-5)⟩⟩]

def t7_337jobs3 : List Job := [⟨plan6230,[⟨3,3,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨15,13,(-2)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_337jobs : List Job := t7_337jobs0++t7_337jobs1++t7_337jobs2++t7_337jobs3




def t7_338root : Job := ⟨plan8836,[],none,⟨21,15,0⟩⟩
def t7_338jobs0 : List Job := [⟨plan6231,[⟨3,0,6⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨10,0,5⟩],(some ⟨10,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨10,1,5⟩],(some ⟨10,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_338jobs1 : List Job := [⟨plan6231,[⟨3,3,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨16,11,(-5)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨15,13,(-2)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_338jobs : List Job := t7_338jobs0++t7_338jobs1




def t7_339root : Job := ⟨plan8837,[],none,⟨21,15,0⟩⟩
def t7_339jobs0 : List Job := [⟨plan8837,[],none,⟨21,15,0⟩⟩]

def t7_339jobs : List Job := t7_339jobs0




def t7_340root : Job := ⟨plan8838,[],none,⟨21,15,0⟩⟩
def t7_340jobs0 : List Job := [⟨plan8838,[],none,⟨21,15,0⟩⟩]

def t7_340jobs : List Job := t7_340jobs0




def t7_341root : Job := ⟨plan8839,[],none,⟨21,15,0⟩⟩
def t7_341jobs0 : List Job := [⟨plan8839,[],none,⟨21,15,0⟩⟩]

def t7_341jobs : List Job := t7_341jobs0




def t7_342root : Job := ⟨plan8655,[],none,⟨21,10,0⟩⟩
def t7_342jobs0 : List Job := [⟨plan8655,[],none,⟨21,10,0⟩⟩]

def t7_342jobs : List Job := t7_342jobs0




def t7_343root : Job := ⟨plan8524,[],none,⟨21,6,0⟩⟩
def t7_343jobs0 : List Job := [⟨plan8524,[],none,⟨21,6,0⟩⟩]

def t7_343jobs : List Job := t7_343jobs0




def t7_344root : Job := ⟨plan8656,[],none,⟨21,10,0⟩⟩
def t7_344jobs0 : List Job := [⟨plan8656,[],none,⟨21,10,0⟩⟩]

def t7_344jobs : List Job := t7_344jobs0




def t7_345root : Job := ⟨plan8657,[],none,⟨21,10,0⟩⟩
def t7_345jobs0 : List Job := [⟨plan8657,[],none,⟨21,10,0⟩⟩]

def t7_345jobs : List Job := t7_345jobs0




def t7_346root : Job := ⟨plan8658,[],none,⟨21,10,0⟩⟩
def t7_346jobs0 : List Job := [⟨plan8658,[],none,⟨21,10,0⟩⟩]

def t7_346jobs : List Job := t7_346jobs0




def t7_347root : Job := ⟨plan8840,[],none,⟨21,15,0⟩⟩
def t7_347jobs0 : List Job := [⟨plan8840,[],none,⟨21,15,0⟩⟩]

def t7_347jobs : List Job := t7_347jobs0




def t7_348root : Job := ⟨plan8841,[],none,⟨21,15,0⟩⟩
def t7_348jobs0 : List Job := [⟨plan8841,[],none,⟨21,15,0⟩⟩]

def t7_348jobs : List Job := t7_348jobs0




def t7_349root : Job := ⟨plan8842,[],none,⟨21,15,0⟩⟩
def t7_349jobs0 : List Job := [⟨plan8842,[],none,⟨21,15,0⟩⟩]

def t7_349jobs : List Job := t7_349jobs0




def t7_350root : Job := ⟨plan8843,[],none,⟨21,15,0⟩⟩
def t7_350jobs0 : List Job := [⟨plan8843,[],none,⟨21,15,0⟩⟩]

def t7_350jobs : List Job := t7_350jobs0




def t7_351root : Job := ⟨plan8844,[],none,⟨21,15,0⟩⟩
def t7_351jobs0 : List Job := [⟨plan8844,[],none,⟨21,15,0⟩⟩]

def t7_351jobs : List Job := t7_351jobs0




def t7_352root : Job := ⟨plan8845,[],none,⟨21,15,0⟩⟩
def t7_352jobs0 : List Job := [⟨plan8845,[],none,⟨21,15,0⟩⟩]

def t7_352jobs : List Job := t7_352jobs0




def t7_353root : Job := ⟨plan8846,[],none,⟨21,15,0⟩⟩
def t7_353jobs0 : List Job := [⟨plan8846,[],none,⟨21,15,0⟩⟩]

def t7_353jobs : List Job := t7_353jobs0




def t7_354root : Job := ⟨plan8847,[],none,⟨21,15,0⟩⟩
def t7_354jobs0 : List Job := [⟨plan8847,[],none,⟨21,15,0⟩⟩]

def t7_354jobs : List Job := t7_354jobs0




def t7_355root : Job := ⟨plan8457,[],none,⟨21,3,0⟩⟩
def t7_355jobs0 : List Job := [⟨plan8457,[],none,⟨21,3,0⟩⟩]

def t7_355jobs : List Job := t7_355jobs0




def t7_356root : Job := ⟨plan8525,[],none,⟨21,6,0⟩⟩
def t7_356jobs0 : List Job := [⟨plan8525,[],none,⟨21,6,0⟩⟩]

def t7_356jobs : List Job := t7_356jobs0




def t7_357root : Job := ⟨plan8526,[],none,⟨21,6,0⟩⟩
def t7_357jobs0 : List Job := [⟨plan8526,[],none,⟨21,6,0⟩⟩]

def t7_357jobs : List Job := t7_357jobs0




def t7_358root : Job := ⟨plan8527,[],none,⟨21,6,0⟩⟩
def t7_358jobs0 : List Job := [⟨plan8527,[],none,⟨21,6,0⟩⟩]

def t7_358jobs : List Job := t7_358jobs0




def t7_359root : Job := ⟨plan8659,[],none,⟨21,10,0⟩⟩
def t7_359jobs0 : List Job := [⟨plan8659,[],none,⟨21,10,0⟩⟩]

def t7_359jobs : List Job := t7_359jobs0




def t7_360root : Job := ⟨plan8660,[],none,⟨21,10,0⟩⟩
def t7_360jobs0 : List Job := [⟨plan8660,[],none,⟨21,10,0⟩⟩]

def t7_360jobs : List Job := t7_360jobs0




def t7_361root : Job := ⟨plan8661,[],none,⟨21,10,0⟩⟩
def t7_361jobs0 : List Job := [⟨plan8661,[],none,⟨21,10,0⟩⟩]

def t7_361jobs : List Job := t7_361jobs0




def t7_362root : Job := ⟨plan8662,[],none,⟨21,10,0⟩⟩
def t7_362jobs0 : List Job := [⟨plan8662,[],none,⟨21,10,0⟩⟩]

def t7_362jobs : List Job := t7_362jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


