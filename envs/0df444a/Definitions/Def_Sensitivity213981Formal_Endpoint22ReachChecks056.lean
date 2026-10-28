-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks056
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks056
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:01.004214+00:00
-- url     : https://prove2.me/theorems/a10ce836-39e2-47d2-bc58-f7b59e999431
-- title:
--   Endpoint22 Reach Checks056 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks056 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_327root`, `ThreeBoundEndpoint22Reachable.t6_327jobs0`, `ThreeBoundEndpoint22Reachable.t6_327jobs`, `ThreeBoundEndpoint22Reachable.t6_328root`, `ThreeBoundEndpoint22Reachable.t6_328jobs0`, `ThreeBoundEndpoint22Reachable.t6_328jobs`, `ThreeBoundEndpoint22Reachable.t6_329root`, `ThreeBoundEndpoint22Reachable.t6_329jobs0`, `ThreeBoundEndpoint22Reachable.t6_329jobs`, `ThreeBoundEndpoint22Reachable.t6_330root`, `ThreeBoundEndpoint22Reachable.t6_330jobs0`, `ThreeBoundEndpoint22Reachable.t6_330jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks056.lean, lines 1–510.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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

def t6_317root : Job := ⟨plan6816,[],none,⟨15,6,0⟩⟩
def t6_317jobs0 : List Job := [⟨plan3434,[⟨1,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,6,(-8)⟩⟩,⟨plan3434,[⟨1,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,6,(-7)⟩⟩,⟨plan3434,[⟨1,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3434,[⟨1,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,6,(-6)⟩⟩,⟨plan3434,[⟨1,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3434,[⟨1,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,6,(-5)⟩⟩,⟨plan3434,[⟨1,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3434,[⟨1,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,6,(-7)⟩⟩,⟨plan3434,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-6)⟩⟩,⟨plan3434,[⟨1,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3434,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-5)⟩⟩,⟨plan3434,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3434,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-4)⟩⟩]

def t6_317jobs1 : List Job := [⟨plan3434,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3434,[⟨1,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3434,[⟨1,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3434,[⟨1,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-8)⟩⟩]

def t6_317jobs2 : List Job := [⟨plan3434,[⟨1,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3434,[⟨1,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-7)⟩⟩]

def t6_317jobs3 : List Job := [⟨plan3434,[⟨1,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-5)⟩⟩,⟨plan3434,[⟨1,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-6)⟩⟩]

def t6_317jobs : List Job := t6_317jobs0++t6_317jobs1++t6_317jobs2++t6_317jobs3




def t6_318root : Job := ⟨plan6817,[],none,⟨15,6,0⟩⟩
def t6_318jobs0 : List Job := [⟨plan5645,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5645,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_318jobs1 : List Job := [⟨plan5645,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_318jobs : List Job := t6_318jobs0++t6_318jobs1




def t6_319root : Job := ⟨plan6818,[],none,⟨15,6,0⟩⟩
def t6_319jobs0 : List Job := [⟨plan6818,[],none,⟨15,6,0⟩⟩]

def t6_319jobs : List Job := t6_319jobs0




def t6_320root : Job := ⟨plan6513,[],none,⟨15,3,0⟩⟩
def t6_320jobs0 : List Job := [⟨plan6513,[],none,⟨15,3,0⟩⟩]

def t6_320jobs : List Job := t6_320jobs0




def t6_321root : Job := ⟨plan6819,[],none,⟨15,6,0⟩⟩
def t6_321jobs0 : List Job := [⟨plan6819,[],none,⟨15,6,0⟩⟩]

def t6_321jobs : List Job := t6_321jobs0




def t6_322root : Job := ⟨plan6820,[],none,⟨15,6,0⟩⟩
def t6_322jobs0 : List Job := [⟨plan6820,[],none,⟨15,6,0⟩⟩]

def t6_322jobs : List Job := t6_322jobs0




def t6_323root : Job := ⟨plan6821,[],none,⟨15,6,0⟩⟩
def t6_323jobs0 : List Job := [⟨plan6821,[],none,⟨15,6,0⟩⟩]

def t6_323jobs : List Job := t6_323jobs0




def t6_324root : Job := ⟨plan6355,[],none,⟨15,1,0⟩⟩
def t6_324jobs0 : List Job := [⟨plan6355,[],none,⟨15,1,0⟩⟩]

def t6_324jobs : List Job := t6_324jobs0




def t6_325root : Job := ⟨plan6514,[],none,⟨15,3,0⟩⟩
def t6_325jobs0 : List Job := [⟨plan6514,[],none,⟨15,3,0⟩⟩]

def t6_325jobs : List Job := t6_325jobs0




def t6_326root : Job := ⟨plan6515,[],none,⟨15,3,0⟩⟩
def t6_326jobs0 : List Job := [⟨plan6515,[],none,⟨15,3,0⟩⟩]

def t6_326jobs : List Job := t6_326jobs0




def t6_327root : Job := ⟨plan6516,[],none,⟨15,3,0⟩⟩
def t6_327jobs0 : List Job := [⟨plan6516,[],none,⟨15,3,0⟩⟩]

def t6_327jobs : List Job := t6_327jobs0




def t6_328root : Job := ⟨plan6822,[],none,⟨15,6,0⟩⟩
def t6_328jobs0 : List Job := [⟨plan6822,[],none,⟨15,6,0⟩⟩]

def t6_328jobs : List Job := t6_328jobs0




def t6_329root : Job := ⟨plan6823,[],none,⟨15,6,0⟩⟩
def t6_329jobs0 : List Job := [⟨plan6823,[],none,⟨15,6,0⟩⟩]

def t6_329jobs : List Job := t6_329jobs0




def t6_330root : Job := ⟨plan6824,[],none,⟨15,6,0⟩⟩
def t6_330jobs0 : List Job := [⟨plan6824,[],none,⟨15,6,0⟩⟩]

def t6_330jobs : List Job := t6_330jobs0




def t6_331root : Job := ⟨plan6825,[],none,⟨15,6,0⟩⟩
def t6_331jobs0 : List Job := [⟨plan6825,[],none,⟨15,6,0⟩⟩]

def t6_331jobs : List Job := t6_331jobs0




def t6_332root : Job := ⟨plan6826,[],none,⟨15,6,0⟩⟩
def t6_332jobs0 : List Job := [⟨plan6826,[],none,⟨15,6,0⟩⟩]

def t6_332jobs : List Job := t6_332jobs0




def t6_333root : Job := ⟨plan6827,[],none,⟨15,6,0⟩⟩
def t6_333jobs0 : List Job := [⟨plan6827,[],none,⟨15,6,0⟩⟩]

def t6_333jobs : List Job := t6_333jobs0




def t6_334root : Job := ⟨plan7212,[],none,⟨15,10,0⟩⟩
def t6_334jobs0 : List Job := [⟨plan7212,[],none,⟨15,10,0⟩⟩]

def t6_334jobs : List Job := t6_334jobs0




def t6_335root : Job := ⟨plan6828,[],none,⟨15,6,0⟩⟩
def t6_335jobs0 : List Job := [⟨plan6828,[],none,⟨15,6,0⟩⟩]

def t6_335jobs : List Job := t6_335jobs0




def t6_336root : Job := ⟨plan7213,[],none,⟨15,10,0⟩⟩
def t6_336jobs0 : List Job := [⟨plan7213,[],none,⟨15,10,0⟩⟩]

def t6_336jobs : List Job := t6_336jobs0




def t6_337root : Job := ⟨plan7214,[],none,⟨15,10,0⟩⟩
def t6_337jobs0 : List Job := [⟨plan7214,[],none,⟨15,10,0⟩⟩]

def t6_337jobs : List Job := t6_337jobs0




def t6_338root : Job := ⟨plan7215,[],none,⟨15,10,0⟩⟩
def t6_338jobs0 : List Job := [⟨plan7215,[],none,⟨15,10,0⟩⟩]

def t6_338jobs : List Job := t6_338jobs0




def t6_339root : Job := ⟨plan7216,[],none,⟨15,10,0⟩⟩
def t6_339jobs0 : List Job := [⟨plan7216,[],none,⟨15,10,0⟩⟩]

def t6_339jobs : List Job := t6_339jobs0




def t6_340root : Job := ⟨plan7217,[],none,⟨15,10,0⟩⟩
def t6_340jobs0 : List Job := [⟨plan7217,[],none,⟨15,10,0⟩⟩]

def t6_340jobs : List Job := t6_340jobs0




def t6_341root : Job := ⟨plan7218,[],none,⟨15,10,0⟩⟩
def t6_341jobs0 : List Job := [⟨plan7218,[],none,⟨15,10,0⟩⟩]

def t6_341jobs : List Job := t6_341jobs0




def t6_342root : Job := ⟨plan7219,[],none,⟨15,10,0⟩⟩
def t6_342jobs0 : List Job := [⟨plan7219,[],none,⟨15,10,0⟩⟩]

def t6_342jobs : List Job := t6_342jobs0




def t6_343root : Job := ⟨plan7220,[],none,⟨15,10,0⟩⟩
def t6_343jobs0 : List Job := [⟨plan7220,[],none,⟨15,10,0⟩⟩]

def t6_343jobs : List Job := t6_343jobs0




def t6_344root : Job := ⟨plan7221,[],none,⟨15,10,0⟩⟩
def t6_344jobs0 : List Job := [⟨plan7221,[],none,⟨15,10,0⟩⟩]

def t6_344jobs : List Job := t6_344jobs0




def t6_345root : Job := ⟨plan7222,[],none,⟨15,10,0⟩⟩
def t6_345jobs0 : List Job := [⟨plan7222,[],none,⟨15,10,0⟩⟩]

def t6_345jobs : List Job := t6_345jobs0




def t6_346root : Job := ⟨plan7223,[],none,⟨15,10,0⟩⟩
def t6_346jobs0 : List Job := [⟨plan7223,[],none,⟨15,10,0⟩⟩]

def t6_346jobs : List Job := t6_346jobs0




def t6_347root : Job := ⟨plan6829,[],none,⟨15,6,0⟩⟩
def t6_347jobs0 : List Job := [⟨plan6829,[],none,⟨15,6,0⟩⟩]

def t6_347jobs : List Job := t6_347jobs0




def t6_348root : Job := ⟨plan7224,[],none,⟨15,10,0⟩⟩
def t6_348jobs0 : List Job := [⟨plan7224,[],none,⟨15,10,0⟩⟩]

def t6_348jobs : List Job := t6_348jobs0




def t6_349root : Job := ⟨plan7225,[],none,⟨15,10,0⟩⟩
def t6_349jobs0 : List Job := [⟨plan7225,[],none,⟨15,10,0⟩⟩]

def t6_349jobs : List Job := t6_349jobs0




def t6_350root : Job := ⟨plan7226,[],none,⟨15,10,0⟩⟩
def t6_350jobs0 : List Job := [⟨plan7226,[],none,⟨15,10,0⟩⟩]

def t6_350jobs : List Job := t6_350jobs0




def t6_351root : Job := ⟨plan7227,[],none,⟨15,10,0⟩⟩
def t6_351jobs0 : List Job := [⟨plan7227,[],none,⟨15,10,0⟩⟩]

def t6_351jobs : List Job := t6_351jobs0




def t6_352root : Job := ⟨plan7228,[],none,⟨15,10,0⟩⟩
def t6_352jobs0 : List Job := [⟨plan7228,[],none,⟨15,10,0⟩⟩]

def t6_352jobs : List Job := t6_352jobs0




def t6_353root : Job := ⟨plan7229,[],none,⟨15,10,0⟩⟩
def t6_353jobs0 : List Job := [⟨plan7229,[],none,⟨15,10,0⟩⟩]

def t6_353jobs : List Job := t6_353jobs0




def t6_354root : Job := ⟨plan6295,[],none,⟨15,0,0⟩⟩
def t6_354jobs0 : List Job := [⟨plan6295,[],none,⟨15,0,0⟩⟩]

def t6_354jobs : List Job := t6_354jobs0




def t6_355root : Job := ⟨plan6356,[],none,⟨15,1,0⟩⟩
def t6_355jobs0 : List Job := [⟨plan6356,[],none,⟨15,1,0⟩⟩]

def t6_355jobs : List Job := t6_355jobs0




def t6_356root : Job := ⟨plan6357,[],none,⟨15,1,0⟩⟩
def t6_356jobs0 : List Job := [⟨plan6357,[],none,⟨15,1,0⟩⟩]

def t6_356jobs : List Job := t6_356jobs0




def t6_357root : Job := ⟨plan6358,[],none,⟨15,1,0⟩⟩
def t6_357jobs0 : List Job := [⟨plan6358,[],none,⟨15,1,0⟩⟩]

def t6_357jobs : List Job := t6_357jobs0




def t6_358root : Job := ⟨plan6517,[],none,⟨15,3,0⟩⟩
def t6_358jobs0 : List Job := [⟨plan6517,[],none,⟨15,3,0⟩⟩]

def t6_358jobs : List Job := t6_358jobs0




def t6_359root : Job := ⟨plan6518,[],none,⟨15,3,0⟩⟩
def t6_359jobs0 : List Job := [⟨plan5505,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5505,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_359jobs1 : List Job := [⟨plan5505,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_359jobs : List Job := t6_359jobs0++t6_359jobs1




def t6_360root : Job := ⟨plan6519,[],none,⟨15,3,0⟩⟩
def t6_360jobs0 : List Job := [⟨plan6519,[],none,⟨15,3,0⟩⟩]

def t6_360jobs : List Job := t6_360jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


