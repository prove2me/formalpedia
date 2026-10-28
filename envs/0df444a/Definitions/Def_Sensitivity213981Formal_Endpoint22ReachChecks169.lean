-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks169
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks169
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:29.113244+00:00
-- url     : https://prove2.me/theorems/846e21b0-aacc-4a8f-8ffd-1778e9e4c9f1
-- title:
--   Endpoint22 Reach Checks169 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks169 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_260jobs0`, `ThreeBoundEndpoint22Reachable.t7_260jobs`, `ThreeBoundEndpoint22Reachable.t7_261root`, `ThreeBoundEndpoint22Reachable.t7_261jobs0`, `ThreeBoundEndpoint22Reachable.t7_261jobs`, `ThreeBoundEndpoint22Reachable.t7_262root`, `ThreeBoundEndpoint22Reachable.t7_262jobs0`, `ThreeBoundEndpoint22Reachable.t7_262jobs`, `ThreeBoundEndpoint22Reachable.t7_263root`, `ThreeBoundEndpoint22Reachable.t7_263jobs0`, `ThreeBoundEndpoint22Reachable.t7_249root`, `ThreeBoundEndpoint22Reachable.t7_263jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks169.lean, lines 1–321.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
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

def t7_248root : Job := ⟨plan8802,[],none,⟨21,15,0⟩⟩
def t7_248jobs0 : List Job := [⟨plan8802,[],none,⟨21,15,0⟩⟩]

def t7_248jobs : List Job := t7_248jobs0




def t7_249root : Job := ⟨plan8803,[],none,⟨21,15,0⟩⟩
def t7_249jobs0 : List Job := [⟨plan8803,[],none,⟨21,15,0⟩⟩]

def t7_249jobs : List Job := t7_249jobs0




def t7_250root : Job := ⟨plan8804,[],none,⟨21,15,0⟩⟩
def t7_250jobs0 : List Job := [⟨plan8804,[],none,⟨21,15,0⟩⟩]

def t7_250jobs : List Job := t7_250jobs0




def t7_251root : Job := ⟨plan8805,[],none,⟨21,15,0⟩⟩
def t7_251jobs0 : List Job := [⟨plan8805,[],none,⟨21,15,0⟩⟩]

def t7_251jobs : List Job := t7_251jobs0




def t7_252root : Job := ⟨plan8806,[],none,⟨21,15,0⟩⟩
def t7_252jobs0 : List Job := [⟨plan8806,[],none,⟨21,15,0⟩⟩]

def t7_252jobs : List Job := t7_252jobs0




def t7_253root : Job := ⟨plan8807,[],none,⟨21,15,0⟩⟩
def t7_253jobs0 : List Job := [⟨plan8319,[⟨2,0,6⟩],(some ⟨2,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8319,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,15,(-5)⟩⟩]

def t7_253jobs1 : List Job := [⟨plan8319,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_253jobs : List Job := t7_253jobs0++t7_253jobs1




def t7_254root : Job := ⟨plan8808,[],none,⟨21,15,0⟩⟩
def t7_254jobs0 : List Job := [⟨plan8320,[⟨2,0,6⟩],(some ⟨2,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8320,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,15,(-5)⟩⟩]

def t7_254jobs1 : List Job := [⟨plan8320,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_254jobs : List Job := t7_254jobs0++t7_254jobs1




def t7_255root : Job := ⟨plan8809,[],none,⟨21,15,0⟩⟩
def t7_255jobs0 : List Job := [⟨plan8809,[],none,⟨21,15,0⟩⟩]

def t7_255jobs : List Job := t7_255jobs0




def t7_256root : Job := ⟨plan8810,[],none,⟨21,15,0⟩⟩
def t7_256jobs0 : List Job := [⟨plan8810,[],none,⟨21,15,0⟩⟩]

def t7_256jobs : List Job := t7_256jobs0




def t7_257root : Job := ⟨plan8811,[],none,⟨21,15,0⟩⟩
def t7_257jobs0 : List Job := [⟨plan8811,[],none,⟨21,15,0⟩⟩]

def t7_257jobs : List Job := t7_257jobs0




def t7_258root : Job := ⟨plan8412,[],none,⟨21,0,0⟩⟩
def t7_258jobs0 : List Job := [⟨plan8412,[],none,⟨21,0,0⟩⟩]

def t7_258jobs : List Job := t7_258jobs0




def t7_259root : Job := ⟨plan8414,[],none,⟨21,0,0⟩⟩
def t7_259jobs0 : List Job := [⟨plan8414,[],none,⟨21,0,0⟩⟩]

def t7_259jobs : List Job := t7_259jobs0




def t7_260root : Job := ⟨plan8415,[],none,⟨21,0,0⟩⟩
def t7_260jobs0 : List Job := [⟨plan8415,[],none,⟨21,0,0⟩⟩]

def t7_260jobs : List Job := t7_260jobs0




def t7_261root : Job := ⟨plan8416,[],none,⟨21,0,0⟩⟩
def t7_261jobs0 : List Job := [⟨plan8416,[],none,⟨21,0,0⟩⟩]

def t7_261jobs : List Job := t7_261jobs0




def t7_262root : Job := ⟨plan8422,[],none,⟨21,1,0⟩⟩
def t7_262jobs0 : List Job := [⟨plan8422,[],none,⟨21,1,0⟩⟩]

def t7_262jobs : List Job := t7_262jobs0




def t7_263root : Job := ⟨plan8423,[],none,⟨21,1,0⟩⟩
def t7_263jobs0 : List Job := [⟨plan8423,[],none,⟨21,1,0⟩⟩]

def t7_263jobs : List Job := t7_263jobs0




def t7_264root : Job := ⟨plan8424,[],none,⟨21,1,0⟩⟩
def t7_264jobs0 : List Job := [⟨plan8424,[],none,⟨21,1,0⟩⟩]

def t7_264jobs : List Job := t7_264jobs0




def t7_265root : Job := ⟨plan8425,[],none,⟨21,1,0⟩⟩
def t7_265jobs0 : List Job := [⟨plan8425,[],none,⟨21,1,0⟩⟩]

def t7_265jobs : List Job := t7_265jobs0




def t7_266root : Job := ⟨plan8426,[],none,⟨21,1,0⟩⟩
def t7_266jobs0 : List Job := [⟨plan8426,[],none,⟨21,1,0⟩⟩]

def t7_266jobs : List Job := t7_266jobs0




def t7_267root : Job := ⟨plan8427,[],none,⟨21,1,0⟩⟩
def t7_267jobs0 : List Job := [⟨plan8427,[],none,⟨21,1,0⟩⟩]

def t7_267jobs : List Job := t7_267jobs0




def t7_268root : Job := ⟨plan8447,[],none,⟨21,3,0⟩⟩
def t7_268jobs0 : List Job := [⟨plan8447,[],none,⟨21,3,0⟩⟩]

def t7_268jobs : List Job := t7_268jobs0




def t7_269root : Job := ⟨plan8448,[],none,⟨21,3,0⟩⟩
def t7_269jobs0 : List Job := [⟨plan8092,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8092,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8092,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,3,(-3)⟩⟩,⟨plan8092,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨19,3,(-1)⟩⟩,⟨plan8092,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,3,(-2)⟩⟩,⟨plan8092,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_269jobs1 : List Job := [⟨plan8092,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨18,3,0⟩⟩,⟨plan8092,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,3,(-1)⟩⟩,⟨plan8092,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,3,(-2)⟩⟩,⟨plan8092,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,3,(-3)⟩⟩]

def t7_269jobs : List Job := t7_269jobs0++t7_269jobs1




def t7_270root : Job := ⟨plan8449,[],none,⟨21,3,0⟩⟩
def t7_270jobs0 : List Job := [⟨plan8449,[],none,⟨21,3,0⟩⟩]

def t7_270jobs : List Job := t7_270jobs0




def t7_271root : Job := ⟨plan8450,[],none,⟨21,3,0⟩⟩
def t7_271jobs0 : List Job := [⟨plan8094,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8094,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8094,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,3,(-3)⟩⟩]

def t7_271jobs1 : List Job := [⟨plan8094,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_271jobs2 : List Job := [⟨plan8094,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_271jobs3 : List Job := [⟨plan8094,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_271jobs4 : List Job := [⟨plan8094,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨18,3,0⟩⟩]

def t7_271jobs5 : List Job := [⟨plan8094,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,3,(-1)⟩⟩,⟨plan8094,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,3,(-2)⟩⟩,⟨plan8094,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,3,(-3)⟩⟩]

def t7_271jobs : List Job := t7_271jobs0++t7_271jobs1++t7_271jobs2++t7_271jobs3++t7_271jobs4++t7_271jobs5




def t7_272root : Job := ⟨plan8451,[],none,⟨21,3,0⟩⟩
def t7_272jobs0 : List Job := [⟨plan8095,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8095,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8095,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,3,(-3)⟩⟩,⟨plan8095,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨19,3,(-1)⟩⟩,⟨plan8095,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_272jobs1 : List Job := [⟨plan8095,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_272jobs2 : List Job := [⟨plan8095,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨18,3,0⟩⟩]

def t7_272jobs3 : List Job := [⟨plan8095,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,3,(-1)⟩⟩,⟨plan8095,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,3,(-2)⟩⟩,⟨plan8095,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,3,(-3)⟩⟩]

def t7_272jobs : List Job := t7_272jobs0++t7_272jobs1++t7_272jobs2++t7_272jobs3




def t7_273root : Job := ⟨plan8452,[],none,⟨21,3,0⟩⟩
def t7_273jobs0 : List Job := [⟨plan8452,[],none,⟨21,3,0⟩⟩]

def t7_273jobs : List Job := t7_273jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


