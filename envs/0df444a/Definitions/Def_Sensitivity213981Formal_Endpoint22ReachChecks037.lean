-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks037
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks037
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:58.758383+00:00
-- url     : https://prove2.me/theorems/11bad7b8-4bcc-4df7-a48e-bfb48dea8771
-- title:
--   Endpoint22 Reach Checks037 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks037 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1242root`, `ThreeBoundEndpoint22Reachable.t5_1242jobs0`, `ThreeBoundEndpoint22Reachable.t5_1242jobs`, `ThreeBoundEndpoint22Reachable.t5_1243root`, `ThreeBoundEndpoint22Reachable.t5_1243jobs0`, `ThreeBoundEndpoint22Reachable.t5_1243jobs`, `ThreeBoundEndpoint22Reachable.t5_1244root`, `ThreeBoundEndpoint22Reachable.t5_1244jobs0`, `ThreeBoundEndpoint22Reachable.t5_1244jobs`, `ThreeBoundEndpoint22Reachable.t5_1245root`, `ThreeBoundEndpoint22Reachable.t5_1245jobs0`, `ThreeBoundEndpoint22Reachable.t5_1245jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks037.lean, lines 1–669.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
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

def t5_1231root : Job := ⟨plan4866,[],none,⟨10,6,0⟩⟩
def t5_1231jobs0 : List Job := [⟨plan4866,[],none,⟨10,6,0⟩⟩]

def t5_1231jobs : List Job := t5_1231jobs0




def t5_1232root : Job := ⟨plan3974,[],none,⟨10,1,0⟩⟩
def t5_1232jobs0 : List Job := [⟨plan3974,[],none,⟨10,1,0⟩⟩]

def t5_1232jobs : List Job := t5_1232jobs0




def t5_1233root : Job := ⟨plan4380,[],none,⟨10,3,0⟩⟩
def t5_1233jobs0 : List Job := [⟨plan4380,[],none,⟨10,3,0⟩⟩]

def t5_1233jobs : List Job := t5_1233jobs0




def t5_1234root : Job := ⟨plan4381,[],none,⟨10,3,0⟩⟩
def t5_1234jobs0 : List Job := [⟨plan2810,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2810,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2810,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2810,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1234jobs1 : List Job := [⟨plan2810,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩,⟨plan2810,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1234jobs : List Job := t5_1234jobs0++t5_1234jobs1




def t5_1235root : Job := ⟨plan4382,[],none,⟨10,3,0⟩⟩
def t5_1235jobs0 : List Job := [⟨plan4382,[],none,⟨10,3,0⟩⟩]

def t5_1235jobs : List Job := t5_1235jobs0




def t5_1236root : Job := ⟨plan4867,[],none,⟨10,6,0⟩⟩
def t5_1236jobs0 : List Job := [⟨plan4867,[],none,⟨10,6,0⟩⟩]

def t5_1236jobs : List Job := t5_1236jobs0




def t5_1237root : Job := ⟨plan4868,[],none,⟨10,6,0⟩⟩
def t5_1237jobs0 : List Job := [⟨plan2968,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2968,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2968,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1237jobs1 : List Job := [⟨plan2968,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan2968,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1237jobs : List Job := t5_1237jobs0++t5_1237jobs1




def t5_1238root : Job := ⟨plan4869,[],none,⟨10,6,0⟩⟩
def t5_1238jobs0 : List Job := [⟨plan4869,[],none,⟨10,6,0⟩⟩]

def t5_1238jobs : List Job := t5_1238jobs0




def t5_1239root : Job := ⟨plan4870,[],none,⟨10,6,0⟩⟩
def t5_1239jobs0 : List Job := [⟨plan4870,[],none,⟨10,6,0⟩⟩]

def t5_1239jobs : List Job := t5_1239jobs0




def t5_1240root : Job := ⟨plan4871,[],none,⟨10,6,0⟩⟩
def t5_1240jobs0 : List Job := [⟨plan2971,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2971,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2971,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1240jobs1 : List Job := [⟨plan2971,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan2971,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1240jobs : List Job := t5_1240jobs0++t5_1240jobs1




def t5_1241root : Job := ⟨plan4872,[],none,⟨10,6,0⟩⟩
def t5_1241jobs0 : List Job := [⟨plan4872,[],none,⟨10,6,0⟩⟩]

def t5_1241jobs : List Job := t5_1241jobs0




def t5_1242root : Job := ⟨plan4383,[],none,⟨10,3,0⟩⟩
def t5_1242jobs0 : List Job := [⟨plan4383,[],none,⟨10,3,0⟩⟩]

def t5_1242jobs : List Job := t5_1242jobs0




def t5_1243root : Job := ⟨plan4873,[],none,⟨10,6,0⟩⟩
def t5_1243jobs0 : List Job := [⟨plan4873,[],none,⟨10,6,0⟩⟩]

def t5_1243jobs : List Job := t5_1243jobs0




def t5_1244root : Job := ⟨plan4874,[],none,⟨10,6,0⟩⟩
def t5_1244jobs0 : List Job := [⟨plan4874,[],none,⟨10,6,0⟩⟩]

def t5_1244jobs : List Job := t5_1244jobs0




def t5_1245root : Job := ⟨plan4875,[],none,⟨10,6,0⟩⟩
def t5_1245jobs0 : List Job := [⟨plan4875,[],none,⟨10,6,0⟩⟩]

def t5_1245jobs : List Job := t5_1245jobs0




def t5_1246root : Job := ⟨plan4876,[],none,⟨10,6,0⟩⟩
def t5_1246jobs0 : List Job := [⟨plan4876,[],none,⟨10,6,0⟩⟩]

def t5_1246jobs : List Job := t5_1246jobs0




def t5_1247root : Job := ⟨plan5123,[],none,⟨10,10,0⟩⟩
def t5_1247jobs0 : List Job := [⟨plan5123,[],none,⟨10,10,0⟩⟩]

def t5_1247jobs : List Job := t5_1247jobs0




def t5_1248root : Job := ⟨plan5124,[],none,⟨10,10,0⟩⟩
def t5_1248jobs0 : List Job := [⟨plan5124,[],none,⟨10,10,0⟩⟩]

def t5_1248jobs : List Job := t5_1248jobs0




def t5_1249root : Job := ⟨plan5125,[],none,⟨10,10,0⟩⟩
def t5_1249jobs0 : List Job := [⟨plan5125,[],none,⟨10,10,0⟩⟩]

def t5_1249jobs : List Job := t5_1249jobs0




def t5_1250root : Job := ⟨plan5126,[],none,⟨10,10,0⟩⟩
def t5_1250jobs0 : List Job := [⟨plan5126,[],none,⟨10,10,0⟩⟩]

def t5_1250jobs : List Job := t5_1250jobs0




def t5_1251root : Job := ⟨plan5127,[],none,⟨10,10,0⟩⟩
def t5_1251jobs0 : List Job := [⟨plan5127,[],none,⟨10,10,0⟩⟩]

def t5_1251jobs : List Job := t5_1251jobs0




def t5_1252root : Job := ⟨plan5128,[],none,⟨10,10,0⟩⟩
def t5_1252jobs0 : List Job := [⟨plan5128,[],none,⟨10,10,0⟩⟩]

def t5_1252jobs : List Job := t5_1252jobs0




def t5_1253root : Job := ⟨plan5129,[],none,⟨10,10,0⟩⟩
def t5_1253jobs0 : List Job := [⟨plan5129,[],none,⟨10,10,0⟩⟩]

def t5_1253jobs : List Job := t5_1253jobs0




def t5_1254root : Job := ⟨plan5130,[],none,⟨10,10,0⟩⟩
def t5_1254jobs0 : List Job := [⟨plan5130,[],none,⟨10,10,0⟩⟩]

def t5_1254jobs : List Job := t5_1254jobs0




def t5_1255root : Job := ⟨plan5131,[],none,⟨10,10,0⟩⟩
def t5_1255jobs0 : List Job := [⟨plan5131,[],none,⟨10,10,0⟩⟩]

def t5_1255jobs : List Job := t5_1255jobs0




def t5_1256root : Job := ⟨plan4877,[],none,⟨10,6,0⟩⟩
def t5_1256jobs0 : List Job := [⟨plan4877,[],none,⟨10,6,0⟩⟩]

def t5_1256jobs : List Job := t5_1256jobs0




def t5_1257root : Job := ⟨plan5132,[],none,⟨10,10,0⟩⟩
def t5_1257jobs0 : List Job := [⟨plan5132,[],none,⟨10,10,0⟩⟩]

def t5_1257jobs : List Job := t5_1257jobs0




def t5_1258root : Job := ⟨plan5133,[],none,⟨10,10,0⟩⟩
def t5_1258jobs0 : List Job := [⟨plan5133,[],none,⟨10,10,0⟩⟩]

def t5_1258jobs : List Job := t5_1258jobs0




def t5_1259root : Job := ⟨plan5134,[],none,⟨10,10,0⟩⟩
def t5_1259jobs0 : List Job := [⟨plan5134,[],none,⟨10,10,0⟩⟩]

def t5_1259jobs : List Job := t5_1259jobs0




def t5_1260root : Job := ⟨plan5135,[],none,⟨10,10,0⟩⟩
def t5_1260jobs0 : List Job := [⟨plan5135,[],none,⟨10,10,0⟩⟩]

def t5_1260jobs : List Job := t5_1260jobs0




def t5_1261root : Job := ⟨plan5136,[],none,⟨10,10,0⟩⟩
def t5_1261jobs0 : List Job := [⟨plan5136,[],none,⟨10,10,0⟩⟩]

def t5_1261jobs : List Job := t5_1261jobs0




def t5_1262root : Job := ⟨plan5137,[],none,⟨10,10,0⟩⟩
def t5_1262jobs0 : List Job := [⟨plan5137,[],none,⟨10,10,0⟩⟩]

def t5_1262jobs : List Job := t5_1262jobs0




def t5_1263root : Job := ⟨plan5138,[],none,⟨10,10,0⟩⟩
def t5_1263jobs0 : List Job := [⟨plan5138,[],none,⟨10,10,0⟩⟩]

def t5_1263jobs : List Job := t5_1263jobs0




def t5_1264root : Job := ⟨plan5139,[],none,⟨10,10,0⟩⟩
def t5_1264jobs0 : List Job := [⟨plan5139,[],none,⟨10,10,0⟩⟩]

def t5_1264jobs : List Job := t5_1264jobs0




def t5_1265root : Job := ⟨plan5140,[],none,⟨10,10,0⟩⟩
def t5_1265jobs0 : List Job := [⟨plan5140,[],none,⟨10,10,0⟩⟩]

def t5_1265jobs : List Job := t5_1265jobs0




def t5_1266root : Job := ⟨plan5141,[],none,⟨10,10,0⟩⟩
def t5_1266jobs0 : List Job := [⟨plan5141,[],none,⟨10,10,0⟩⟩]

def t5_1266jobs : List Job := t5_1266jobs0




def t5_1267root : Job := ⟨plan5142,[],none,⟨10,10,0⟩⟩
def t5_1267jobs0 : List Job := [⟨plan5142,[],none,⟨10,10,0⟩⟩]

def t5_1267jobs : List Job := t5_1267jobs0




def t5_1268root : Job := ⟨plan5143,[],none,⟨10,10,0⟩⟩
def t5_1268jobs0 : List Job := [⟨plan5143,[],none,⟨10,10,0⟩⟩]

def t5_1268jobs : List Job := t5_1268jobs0




def t5_1269root : Job := ⟨plan5144,[],none,⟨10,10,0⟩⟩
def t5_1269jobs0 : List Job := [⟨plan5144,[],none,⟨10,10,0⟩⟩]

def t5_1269jobs : List Job := t5_1269jobs0




def t5_1270root : Job := ⟨plan4384,[],none,⟨10,3,0⟩⟩
def t5_1270jobs0 : List Job := [⟨plan4384,[],none,⟨10,3,0⟩⟩]

def t5_1270jobs : List Job := t5_1270jobs0




def t5_1271root : Job := ⟨plan4878,[],none,⟨10,6,0⟩⟩
def t5_1271jobs0 : List Job := [⟨plan4878,[],none,⟨10,6,0⟩⟩]

def t5_1271jobs : List Job := t5_1271jobs0




def t5_1272root : Job := ⟨plan4879,[],none,⟨10,6,0⟩⟩
def t5_1272jobs0 : List Job := [⟨plan4879,[],none,⟨10,6,0⟩⟩]

def t5_1272jobs : List Job := t5_1272jobs0




def t5_1273root : Job := ⟨plan4880,[],none,⟨10,6,0⟩⟩
def t5_1273jobs0 : List Job := [⟨plan4880,[],none,⟨10,6,0⟩⟩]

def t5_1273jobs : List Job := t5_1273jobs0




def t5_1274root : Job := ⟨plan5145,[],none,⟨10,10,0⟩⟩
def t5_1274jobs0 : List Job := [⟨plan5145,[],none,⟨10,10,0⟩⟩]

def t5_1274jobs : List Job := t5_1274jobs0




def t5_1275root : Job := ⟨plan5146,[],none,⟨10,10,0⟩⟩
def t5_1275jobs0 : List Job := [⟨plan5146,[],none,⟨10,10,0⟩⟩]

def t5_1275jobs : List Job := t5_1275jobs0




def t5_1276root : Job := ⟨plan5147,[],none,⟨10,10,0⟩⟩
def t5_1276jobs0 : List Job := [⟨plan5147,[],none,⟨10,10,0⟩⟩]

def t5_1276jobs : List Job := t5_1276jobs0




def t5_1277root : Job := ⟨plan5148,[],none,⟨10,10,0⟩⟩
def t5_1277jobs0 : List Job := [⟨plan5148,[],none,⟨10,10,0⟩⟩]

def t5_1277jobs : List Job := t5_1277jobs0




def t5_1278root : Job := ⟨plan4881,[],none,⟨10,6,0⟩⟩
def t5_1278jobs0 : List Job := [⟨plan4881,[],none,⟨10,6,0⟩⟩]

def t5_1278jobs : List Job := t5_1278jobs0




def t5_1279root : Job := ⟨plan5149,[],none,⟨10,10,0⟩⟩
def t5_1279jobs0 : List Job := [⟨plan5149,[],none,⟨10,10,0⟩⟩]

def t5_1279jobs : List Job := t5_1279jobs0




def t5_1280root : Job := ⟨plan5150,[],none,⟨10,10,0⟩⟩
def t5_1280jobs0 : List Job := [⟨plan5150,[],none,⟨10,10,0⟩⟩]

def t5_1280jobs : List Job := t5_1280jobs0




def t5_1281root : Job := ⟨plan5151,[],none,⟨10,10,0⟩⟩
def t5_1281jobs0 : List Job := [⟨plan5151,[],none,⟨10,10,0⟩⟩]

def t5_1281jobs : List Job := t5_1281jobs0




def t5_1282root : Job := ⟨plan5152,[],none,⟨10,10,0⟩⟩
def t5_1282jobs0 : List Job := [⟨plan5152,[],none,⟨10,10,0⟩⟩]

def t5_1282jobs : List Job := t5_1282jobs0




def t5_1283root : Job := ⟨plan5153,[],none,⟨10,10,0⟩⟩
def t5_1283jobs0 : List Job := [⟨plan5153,[],none,⟨10,10,0⟩⟩]

def t5_1283jobs : List Job := t5_1283jobs0




def t5_1284root : Job := ⟨plan5154,[],none,⟨10,10,0⟩⟩
def t5_1284jobs0 : List Job := [⟨plan5154,[],none,⟨10,10,0⟩⟩]

def t5_1284jobs : List Job := t5_1284jobs0




def t5_1285root : Job := ⟨plan5155,[],none,⟨10,10,0⟩⟩
def t5_1285jobs0 : List Job := [⟨plan5155,[],none,⟨10,10,0⟩⟩]

def t5_1285jobs : List Job := t5_1285jobs0




def t5_1286root : Job := ⟨plan5156,[],none,⟨10,10,0⟩⟩
def t5_1286jobs0 : List Job := [⟨plan5156,[],none,⟨10,10,0⟩⟩]

def t5_1286jobs : List Job := t5_1286jobs0




def t5_1287root : Job := ⟨plan5157,[],none,⟨10,10,0⟩⟩
def t5_1287jobs0 : List Job := [⟨plan5157,[],none,⟨10,10,0⟩⟩]

def t5_1287jobs : List Job := t5_1287jobs0




def t5_1288root : Job := ⟨plan5158,[],none,⟨10,10,0⟩⟩
def t5_1288jobs0 : List Job := [⟨plan5158,[],none,⟨10,10,0⟩⟩]

def t5_1288jobs : List Job := t5_1288jobs0




def t5_1289root : Job := ⟨plan5159,[],none,⟨10,10,0⟩⟩
def t5_1289jobs0 : List Job := [⟨plan5159,[],none,⟨10,10,0⟩⟩]

def t5_1289jobs : List Job := t5_1289jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


