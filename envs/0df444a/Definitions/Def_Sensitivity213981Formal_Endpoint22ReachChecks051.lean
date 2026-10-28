-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks051
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks051
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:29.727247+00:00
-- url     : https://prove2.me/theorems/c36c058a-2209-4346-a981-459883b9eef2
-- title:
--   Endpoint22 Reach Checks051 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks051 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_269root`, `ThreeBoundEndpoint22Reachable.t6_269jobs0`, `ThreeBoundEndpoint22Reachable.t6_269jobs`, `ThreeBoundEndpoint22Reachable.t6_270root`, `ThreeBoundEndpoint22Reachable.t6_270jobs0`, `ThreeBoundEndpoint22Reachable.t6_270jobs`, `ThreeBoundEndpoint22Reachable.t6_271root`, `ThreeBoundEndpoint22Reachable.t6_271jobs0`, `ThreeBoundEndpoint22Reachable.t6_271jobs`, `ThreeBoundEndpoint22Reachable.t6_258root`, `ThreeBoundEndpoint22Reachable.t6_272root`, `ThreeBoundEndpoint22Reachable.t6_272jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks051.lean, lines 1–287.

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

def t6_257root : Job := ⟨plan6780,[],none,⟨15,6,0⟩⟩
def t6_257jobs0 : List Job := [⟨plan6780,[],none,⟨15,6,0⟩⟩]

def t6_257jobs : List Job := t6_257jobs0




def t6_258root : Job := ⟨plan6781,[],none,⟨15,6,0⟩⟩
def t6_258jobs0 : List Job := [⟨plan6781,[],none,⟨15,6,0⟩⟩]

def t6_258jobs : List Job := t6_258jobs0




def t6_259root : Job := ⟨plan6782,[],none,⟨15,6,0⟩⟩
def t6_259jobs0 : List Job := [⟨plan6782,[],none,⟨15,6,0⟩⟩]

def t6_259jobs : List Job := t6_259jobs0




def t6_260root : Job := ⟨plan6783,[],none,⟨15,6,0⟩⟩
def t6_260jobs0 : List Job := [⟨plan6783,[],none,⟨15,6,0⟩⟩]

def t6_260jobs : List Job := t6_260jobs0




def t6_261root : Job := ⟨plan6784,[],none,⟨15,6,0⟩⟩
def t6_261jobs0 : List Job := [⟨plan6784,[],none,⟨15,6,0⟩⟩]

def t6_261jobs : List Job := t6_261jobs0




def t6_262root : Job := ⟨plan6785,[],none,⟨15,6,0⟩⟩
def t6_262jobs0 : List Job := [⟨plan5594,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5594,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_262jobs1 : List Job := [⟨plan5594,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_262jobs : List Job := t6_262jobs0++t6_262jobs1




def t6_263root : Job := ⟨plan6786,[],none,⟨15,6,0⟩⟩
def t6_263jobs0 : List Job := [⟨plan6786,[],none,⟨15,6,0⟩⟩]

def t6_263jobs : List Job := t6_263jobs0




def t6_264root : Job := ⟨plan6787,[],none,⟨15,6,0⟩⟩
def t6_264jobs0 : List Job := [⟨plan6787,[],none,⟨15,6,0⟩⟩]

def t6_264jobs : List Job := t6_264jobs0




def t6_265root : Job := ⟨plan6788,[],none,⟨15,6,0⟩⟩
def t6_265jobs0 : List Job := [⟨plan5597,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5597,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_265jobs1 : List Job := [⟨plan5597,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_265jobs : List Job := t6_265jobs0++t6_265jobs1




def t6_266root : Job := ⟨plan6789,[],none,⟨15,6,0⟩⟩
def t6_266jobs0 : List Job := [⟨plan5598,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_266jobs1 : List Job := [⟨plan5598,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_266jobs2 : List Job := [⟨plan5598,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_266jobs : List Job := t6_266jobs0++t6_266jobs1++t6_266jobs2




def t6_267root : Job := ⟨plan6790,[],none,⟨15,6,0⟩⟩
def t6_267jobs0 : List Job := [⟨plan6790,[],none,⟨15,6,0⟩⟩]

def t6_267jobs : List Job := t6_267jobs0




def t6_268root : Job := ⟨plan6791,[],none,⟨15,6,0⟩⟩
def t6_268jobs0 : List Job := [⟨plan6791,[],none,⟨15,6,0⟩⟩]

def t6_268jobs : List Job := t6_268jobs0




def t6_269root : Job := ⟨plan6792,[],none,⟨15,6,0⟩⟩
def t6_269jobs0 : List Job := [⟨plan6792,[],none,⟨15,6,0⟩⟩]

def t6_269jobs : List Job := t6_269jobs0




def t6_270root : Job := ⟨plan6348,[],none,⟨15,1,0⟩⟩
def t6_270jobs0 : List Job := [⟨plan6348,[],none,⟨15,1,0⟩⟩]

def t6_270jobs : List Job := t6_270jobs0




def t6_271root : Job := ⟨plan6500,[],none,⟨15,3,0⟩⟩
def t6_271jobs0 : List Job := [⟨plan6500,[],none,⟨15,3,0⟩⟩]

def t6_271jobs : List Job := t6_271jobs0




def t6_272root : Job := ⟨plan6501,[],none,⟨15,3,0⟩⟩
def t6_272jobs0 : List Job := [⟨plan5476,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5476,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_272jobs1 : List Job := [⟨plan5476,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_272jobs : List Job := t6_272jobs0++t6_272jobs1




def t6_273root : Job := ⟨plan6502,[],none,⟨15,3,0⟩⟩
def t6_273jobs0 : List Job := [⟨plan6502,[],none,⟨15,3,0⟩⟩]

def t6_273jobs : List Job := t6_273jobs0




def t6_274root : Job := ⟨plan6793,[],none,⟨15,6,0⟩⟩
def t6_274jobs0 : List Job := [⟨plan6793,[],none,⟨15,6,0⟩⟩]

def t6_274jobs : List Job := t6_274jobs0




def t6_275root : Job := ⟨plan6794,[],none,⟨15,6,0⟩⟩
def t6_275jobs0 : List Job := [⟨plan6794,[],none,⟨15,6,0⟩⟩]

def t6_275jobs : List Job := t6_275jobs0




def t6_276root : Job := ⟨plan6795,[],none,⟨15,6,0⟩⟩
def t6_276jobs0 : List Job := [⟨plan6795,[],none,⟨15,6,0⟩⟩]

def t6_276jobs : List Job := t6_276jobs0




def t6_277root : Job := ⟨plan6796,[],none,⟨15,6,0⟩⟩
def t6_277jobs0 : List Job := [⟨plan6796,[],none,⟨15,6,0⟩⟩]

def t6_277jobs : List Job := t6_277jobs0




def t6_278root : Job := ⟨plan6797,[],none,⟨15,6,0⟩⟩
def t6_278jobs0 : List Job := [⟨plan6797,[],none,⟨15,6,0⟩⟩]

def t6_278jobs : List Job := t6_278jobs0




def t6_279root : Job := ⟨plan6798,[],none,⟨15,6,0⟩⟩
def t6_279jobs0 : List Job := [⟨plan6798,[],none,⟨15,6,0⟩⟩]

def t6_279jobs : List Job := t6_279jobs0




def t6_280root : Job := ⟨plan6799,[],none,⟨15,6,0⟩⟩
def t6_280jobs0 : List Job := [⟨plan6799,[],none,⟨15,6,0⟩⟩]

def t6_280jobs : List Job := t6_280jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


