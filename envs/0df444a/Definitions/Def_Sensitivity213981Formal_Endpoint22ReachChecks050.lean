-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks050
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks050
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:23:39.787979+00:00
-- url     : https://prove2.me/theorems/18b2ac31-407e-4d0f-93f8-14f0e9c2989c
-- title:
--   Endpoint22 Reach Checks050 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks050 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_246root`, `ThreeBoundEndpoint22Reachable.t6_246jobs0`, `ThreeBoundEndpoint22Reachable.t6_246jobs`, `ThreeBoundEndpoint22Reachable.t6_247root`, `ThreeBoundEndpoint22Reachable.t6_247jobs0`, `ThreeBoundEndpoint22Reachable.t6_247jobs`, `ThreeBoundEndpoint22Reachable.t6_248root`, `ThreeBoundEndpoint22Reachable.t6_248jobs0`, `ThreeBoundEndpoint22Reachable.t6_248jobs`, `ThreeBoundEndpoint22Reachable.t6_249root`, `ThreeBoundEndpoint22Reachable.t6_249jobs0`, `ThreeBoundEndpoint22Reachable.t6_249jobs1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks050.lean, lines 1–218.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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

def t6_240root : Job := ⟨plan6490,[],none,⟨15,3,0⟩⟩
def t6_240jobs0 : List Job := [⟨plan3315,[⟨1,0,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_240jobs1 : List Job := [⟨plan3315,[⟨1,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-4)⟩⟩]

def t6_240jobs2 : List Job := [⟨plan3315,[⟨1,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-6)⟩⟩]

def t6_240jobs : List Job := t6_240jobs0++t6_240jobs1++t6_240jobs2




def t6_241root : Job := ⟨plan6491,[],none,⟨15,3,0⟩⟩
def t6_241jobs0 : List Job := [⟨plan3316,[⟨1,0,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_241jobs1 : List Job := [⟨plan3316,[⟨1,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-4)⟩⟩]

def t6_241jobs2 : List Job := [⟨plan3316,[⟨1,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-6)⟩⟩]

def t6_241jobs : List Job := t6_241jobs0++t6_241jobs1++t6_241jobs2




def t6_242root : Job := ⟨plan6492,[],none,⟨15,3,0⟩⟩
def t6_242jobs0 : List Job := [⟨plan6492,[],none,⟨15,3,0⟩⟩]

def t6_242jobs : List Job := t6_242jobs0




def t6_243root : Job := ⟨plan6493,[],none,⟨15,3,0⟩⟩
def t6_243jobs0 : List Job := [⟨plan5459,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5459,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_243jobs1 : List Job := [⟨plan5459,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_243jobs : List Job := t6_243jobs0++t6_243jobs1




def t6_244root : Job := ⟨plan6494,[],none,⟨15,3,0⟩⟩
def t6_244jobs0 : List Job := [⟨plan3319,[⟨1,0,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_244jobs1 : List Job := [⟨plan3319,[⟨1,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-4)⟩⟩]

def t6_244jobs2 : List Job := [⟨plan3319,[⟨1,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-6)⟩⟩]

def t6_244jobs : List Job := t6_244jobs0++t6_244jobs1++t6_244jobs2




def t6_245root : Job := ⟨plan6495,[],none,⟨15,3,0⟩⟩
def t6_245jobs0 : List Job := [⟨plan5461,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5461,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_245jobs1 : List Job := [⟨plan5461,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_245jobs : List Job := t6_245jobs0++t6_245jobs1




def t6_246root : Job := ⟨plan6496,[],none,⟨15,3,0⟩⟩
def t6_246jobs0 : List Job := [⟨plan6496,[],none,⟨15,3,0⟩⟩]

def t6_246jobs : List Job := t6_246jobs0




def t6_247root : Job := ⟨plan6347,[],none,⟨15,1,0⟩⟩
def t6_247jobs0 : List Job := [⟨plan6347,[],none,⟨15,1,0⟩⟩]

def t6_247jobs : List Job := t6_247jobs0




def t6_248root : Job := ⟨plan6497,[],none,⟨15,3,0⟩⟩
def t6_248jobs0 : List Job := [⟨plan6497,[],none,⟨15,3,0⟩⟩]

def t6_248jobs : List Job := t6_248jobs0




def t6_249root : Job := ⟨plan6498,[],none,⟨15,3,0⟩⟩
def t6_249jobs0 : List Job := [⟨plan5467,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5467,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_249jobs1 : List Job := [⟨plan5467,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_249jobs : List Job := t6_249jobs0++t6_249jobs1




def t6_250root : Job := ⟨plan6499,[],none,⟨15,3,0⟩⟩
def t6_250jobs0 : List Job := [⟨plan6499,[],none,⟨15,3,0⟩⟩]

def t6_250jobs : List Job := t6_250jobs0




def t6_251root : Job := ⟨plan6774,[],none,⟨15,6,0⟩⟩
def t6_251jobs0 : List Job := [⟨plan6774,[],none,⟨15,6,0⟩⟩]

def t6_251jobs : List Job := t6_251jobs0




def t6_252root : Job := ⟨plan6775,[],none,⟨15,6,0⟩⟩
def t6_252jobs0 : List Job := [⟨plan6775,[],none,⟨15,6,0⟩⟩]

def t6_252jobs : List Job := t6_252jobs0




def t6_253root : Job := ⟨plan6776,[],none,⟨15,6,0⟩⟩
def t6_253jobs0 : List Job := [⟨plan6776,[],none,⟨15,6,0⟩⟩]

def t6_253jobs : List Job := t6_253jobs0




def t6_254root : Job := ⟨plan6777,[],none,⟨15,6,0⟩⟩
def t6_254jobs0 : List Job := [⟨plan6777,[],none,⟨15,6,0⟩⟩]

def t6_254jobs : List Job := t6_254jobs0




def t6_255root : Job := ⟨plan6778,[],none,⟨15,6,0⟩⟩
def t6_255jobs0 : List Job := [⟨plan6778,[],none,⟨15,6,0⟩⟩]

def t6_255jobs : List Job := t6_255jobs0




def t6_256root : Job := ⟨plan6779,[],none,⟨15,6,0⟩⟩
def t6_256jobs0 : List Job := [⟨plan6779,[],none,⟨15,6,0⟩⟩]

def t6_256jobs : List Job := t6_256jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


