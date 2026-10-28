-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks133
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks133
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:32.726615+00:00
-- url     : https://prove2.me/theorems/20837d7d-ad28-4f7d-a43d-3f092031238e
-- title:
--   Endpoint22 Reach Checks133 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks133 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1245root`, `ThreeBoundEndpoint22Reachable.t6_1245jobs0`, `ThreeBoundEndpoint22Reachable.t6_1245jobs`, `ThreeBoundEndpoint22Reachable.t6_1235jobs2`, `ThreeBoundEndpoint22Reachable.t6_1246root`, `ThreeBoundEndpoint22Reachable.t6_1246jobs0`, `ThreeBoundEndpoint22Reachable.t6_1246jobs`, `ThreeBoundEndpoint22Reachable.t6_1247root`, `ThreeBoundEndpoint22Reachable.t6_1247jobs0`, `ThreeBoundEndpoint22Reachable.t6_1247jobs`, `ThreeBoundEndpoint22Reachable.t6_1235jobs`, `ThreeBoundEndpoint22Reachable.t6_1248root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks133.lean, lines 1–611.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans081
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

def t6_1235root : Job := ⟨plan7548,[],none,⟨15,10,0⟩⟩
def t6_1235jobs0 : List Job := [⟨plan5817,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5817,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1235jobs1 : List Job := [⟨plan5817,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5817,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1235jobs2 : List Job := [⟨plan5817,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1235jobs : List Job := t6_1235jobs0++t6_1235jobs1++t6_1235jobs2




def t6_1236root : Job := ⟨plan7549,[],none,⟨15,10,0⟩⟩
def t6_1236jobs0 : List Job := [⟨plan5818,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5818,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5818,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1236jobs1 : List Job := [⟨plan5818,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩,⟨plan5818,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1236jobs : List Job := t6_1236jobs0++t6_1236jobs1




def t6_1237root : Job := ⟨plan7550,[],none,⟨15,10,0⟩⟩
def t6_1237jobs0 : List Job := [⟨plan7550,[],none,⟨15,10,0⟩⟩]

def t6_1237jobs : List Job := t6_1237jobs0




def t6_1238root : Job := ⟨plan7551,[],none,⟨15,10,0⟩⟩
def t6_1238jobs0 : List Job := [⟨plan5820,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5820,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1238jobs1 : List Job := [⟨plan5820,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5820,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩,⟨plan5820,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1238jobs : List Job := t6_1238jobs0++t6_1238jobs1




def t6_1239root : Job := ⟨plan7552,[],none,⟨15,10,0⟩⟩
def t6_1239jobs0 : List Job := [⟨plan5821,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5821,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1239jobs1 : List Job := [⟨plan5821,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5821,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1239jobs2 : List Job := [⟨plan5821,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1239jobs : List Job := t6_1239jobs0++t6_1239jobs1++t6_1239jobs2




def t6_1240root : Job := ⟨plan7553,[],none,⟨15,10,0⟩⟩
def t6_1240jobs0 : List Job := [⟨plan5822,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5822,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5822,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5822,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1240jobs1 : List Job := [⟨plan5822,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1240jobs : List Job := t6_1240jobs0++t6_1240jobs1




def t6_1241root : Job := ⟨plan7554,[],none,⟨15,10,0⟩⟩
def t6_1241jobs0 : List Job := [⟨plan7554,[],none,⟨15,10,0⟩⟩]

def t6_1241jobs : List Job := t6_1241jobs0




def t6_1242root : Job := ⟨plan6653,[],none,⟨15,3,0⟩⟩
def t6_1242jobs0 : List Job := [⟨plan6653,[],none,⟨15,3,0⟩⟩]

def t6_1242jobs : List Job := t6_1242jobs0




def t6_1243root : Job := ⟨plan7059,[],none,⟨15,6,0⟩⟩
def t6_1243jobs0 : List Job := [⟨plan7059,[],none,⟨15,6,0⟩⟩]

def t6_1243jobs : List Job := t6_1243jobs0




def t6_1244root : Job := ⟨plan7060,[],none,⟨15,6,0⟩⟩
def t6_1244jobs0 : List Job := [⟨plan7060,[],none,⟨15,6,0⟩⟩]

def t6_1244jobs : List Job := t6_1244jobs0




def t6_1245root : Job := ⟨plan7061,[],none,⟨15,6,0⟩⟩
def t6_1245jobs0 : List Job := [⟨plan7061,[],none,⟨15,6,0⟩⟩]

def t6_1245jobs : List Job := t6_1245jobs0




def t6_1246root : Job := ⟨plan7555,[],none,⟨15,10,0⟩⟩
def t6_1246jobs0 : List Job := [⟨plan7555,[],none,⟨15,10,0⟩⟩]

def t6_1246jobs : List Job := t6_1246jobs0




def t6_1247root : Job := ⟨plan7556,[],none,⟨15,10,0⟩⟩
def t6_1247jobs0 : List Job := [⟨plan7556,[],none,⟨15,10,0⟩⟩]

def t6_1247jobs : List Job := t6_1247jobs0




def t6_1248root : Job := ⟨plan7557,[],none,⟨15,10,0⟩⟩
def t6_1248jobs0 : List Job := [⟨plan7557,[],none,⟨15,10,0⟩⟩]

def t6_1248jobs : List Job := t6_1248jobs0




def t6_1249root : Job := ⟨plan7558,[],none,⟨15,10,0⟩⟩
def t6_1249jobs0 : List Job := [⟨plan7558,[],none,⟨15,10,0⟩⟩]

def t6_1249jobs : List Job := t6_1249jobs0




def t6_1250root : Job := ⟨plan7559,[],none,⟨15,10,0⟩⟩
def t6_1250jobs0 : List Job := [⟨plan7559,[],none,⟨15,10,0⟩⟩]

def t6_1250jobs : List Job := t6_1250jobs0




def t6_1251root : Job := ⟨plan7560,[],none,⟨15,10,0⟩⟩
def t6_1251jobs0 : List Job := [⟨plan7560,[],none,⟨15,10,0⟩⟩]

def t6_1251jobs : List Job := t6_1251jobs0




def t6_1252root : Job := ⟨plan7561,[],none,⟨15,10,0⟩⟩
def t6_1252jobs0 : List Job := [⟨plan7561,[],none,⟨15,10,0⟩⟩]

def t6_1252jobs : List Job := t6_1252jobs0




def t6_1253root : Job := ⟨plan7812,[],none,⟨15,15,0⟩⟩
def t6_1253jobs0 : List Job := [⟨plan7812,[],none,⟨15,15,0⟩⟩]

def t6_1253jobs : List Job := t6_1253jobs0




def t6_1254root : Job := ⟨plan7813,[],none,⟨15,15,0⟩⟩
def t6_1254jobs0 : List Job := [⟨plan7813,[],none,⟨15,15,0⟩⟩]

def t6_1254jobs : List Job := t6_1254jobs0




def t6_1255root : Job := ⟨plan7814,[],none,⟨15,15,0⟩⟩
def t6_1255jobs0 : List Job := [⟨plan7814,[],none,⟨15,15,0⟩⟩]

def t6_1255jobs : List Job := t6_1255jobs0




def t6_1256root : Job := ⟨plan7815,[],none,⟨15,15,0⟩⟩
def t6_1256jobs0 : List Job := [⟨plan7815,[],none,⟨15,15,0⟩⟩]

def t6_1256jobs : List Job := t6_1256jobs0




def t6_1257root : Job := ⟨plan7816,[],none,⟨15,15,0⟩⟩
def t6_1257jobs0 : List Job := [⟨plan7816,[],none,⟨15,15,0⟩⟩]

def t6_1257jobs : List Job := t6_1257jobs0




def t6_1258root : Job := ⟨plan7817,[],none,⟨15,15,0⟩⟩
def t6_1258jobs0 : List Job := [⟨plan7817,[],none,⟨15,15,0⟩⟩]

def t6_1258jobs : List Job := t6_1258jobs0




def t6_1259root : Job := ⟨plan7818,[],none,⟨15,15,0⟩⟩
def t6_1259jobs0 : List Job := [⟨plan7818,[],none,⟨15,15,0⟩⟩]

def t6_1259jobs : List Job := t6_1259jobs0




def t6_1260root : Job := ⟨plan7819,[],none,⟨15,15,0⟩⟩
def t6_1260jobs0 : List Job := [⟨plan7819,[],none,⟨15,15,0⟩⟩]

def t6_1260jobs : List Job := t6_1260jobs0




def t6_1261root : Job := ⟨plan7820,[],none,⟨15,15,0⟩⟩
def t6_1261jobs0 : List Job := [⟨plan7820,[],none,⟨15,15,0⟩⟩]

def t6_1261jobs : List Job := t6_1261jobs0




def t6_1262root : Job := ⟨plan7821,[],none,⟨15,15,0⟩⟩
def t6_1262jobs0 : List Job := [⟨plan7821,[],none,⟨15,15,0⟩⟩]

def t6_1262jobs : List Job := t6_1262jobs0




def t6_1263root : Job := ⟨plan7562,[],none,⟨15,10,0⟩⟩
def t6_1263jobs0 : List Job := [⟨plan7562,[],none,⟨15,10,0⟩⟩]

def t6_1263jobs : List Job := t6_1263jobs0




def t6_1264root : Job := ⟨plan7822,[],none,⟨15,15,0⟩⟩
def t6_1264jobs0 : List Job := [⟨plan7822,[],none,⟨15,15,0⟩⟩]

def t6_1264jobs : List Job := t6_1264jobs0




def t6_1265root : Job := ⟨plan7823,[],none,⟨15,15,0⟩⟩
def t6_1265jobs0 : List Job := [⟨plan7823,[],none,⟨15,15,0⟩⟩]

def t6_1265jobs : List Job := t6_1265jobs0




def t6_1266root : Job := ⟨plan7824,[],none,⟨15,15,0⟩⟩
def t6_1266jobs0 : List Job := [⟨plan7824,[],none,⟨15,15,0⟩⟩]

def t6_1266jobs : List Job := t6_1266jobs0




def t6_1267root : Job := ⟨plan7825,[],none,⟨15,15,0⟩⟩
def t6_1267jobs0 : List Job := [⟨plan7825,[],none,⟨15,15,0⟩⟩]

def t6_1267jobs : List Job := t6_1267jobs0




def t6_1268root : Job := ⟨plan7826,[],none,⟨15,15,0⟩⟩
def t6_1268jobs0 : List Job := [⟨plan7826,[],none,⟨15,15,0⟩⟩]

def t6_1268jobs : List Job := t6_1268jobs0




def t6_1269root : Job := ⟨plan7827,[],none,⟨15,15,0⟩⟩
def t6_1269jobs0 : List Job := [⟨plan7827,[],none,⟨15,15,0⟩⟩]

def t6_1269jobs : List Job := t6_1269jobs0




def t6_1270root : Job := ⟨plan7828,[],none,⟨15,15,0⟩⟩
def t6_1270jobs0 : List Job := [⟨plan7828,[],none,⟨15,15,0⟩⟩]

def t6_1270jobs : List Job := t6_1270jobs0




def t6_1271root : Job := ⟨plan7829,[],none,⟨15,15,0⟩⟩
def t6_1271jobs0 : List Job := [⟨plan7829,[],none,⟨15,15,0⟩⟩]

def t6_1271jobs : List Job := t6_1271jobs0




def t6_1272root : Job := ⟨plan7830,[],none,⟨15,15,0⟩⟩
def t6_1272jobs0 : List Job := [⟨plan7830,[],none,⟨15,15,0⟩⟩]

def t6_1272jobs : List Job := t6_1272jobs0




def t6_1273root : Job := ⟨plan7831,[],none,⟨15,15,0⟩⟩
def t6_1273jobs0 : List Job := [⟨plan7831,[],none,⟨15,15,0⟩⟩]

def t6_1273jobs : List Job := t6_1273jobs0




def t6_1274root : Job := ⟨plan7832,[],none,⟨15,15,0⟩⟩
def t6_1274jobs0 : List Job := [⟨plan7832,[],none,⟨15,15,0⟩⟩]

def t6_1274jobs : List Job := t6_1274jobs0




def t6_1275root : Job := ⟨plan7833,[],none,⟨15,15,0⟩⟩
def t6_1275jobs0 : List Job := [⟨plan7833,[],none,⟨15,15,0⟩⟩]

def t6_1275jobs : List Job := t6_1275jobs0




def t6_1276root : Job := ⟨plan7834,[],none,⟨15,15,0⟩⟩
def t6_1276jobs0 : List Job := [⟨plan7834,[],none,⟨15,15,0⟩⟩]

def t6_1276jobs : List Job := t6_1276jobs0




def t6_1277root : Job := ⟨plan7835,[],none,⟨15,15,0⟩⟩
def t6_1277jobs0 : List Job := [⟨plan7835,[],none,⟨15,15,0⟩⟩]

def t6_1277jobs : List Job := t6_1277jobs0




def t6_1278root : Job := ⟨plan7836,[],none,⟨15,15,0⟩⟩
def t6_1278jobs0 : List Job := [⟨plan7836,[],none,⟨15,15,0⟩⟩]

def t6_1278jobs : List Job := t6_1278jobs0




def t6_1279root : Job := ⟨plan7837,[],none,⟨15,15,0⟩⟩
def t6_1279jobs0 : List Job := [⟨plan7837,[],none,⟨15,15,0⟩⟩]

def t6_1279jobs : List Job := t6_1279jobs0




def t6_1280root : Job := ⟨plan7838,[],none,⟨15,15,0⟩⟩
def t6_1280jobs0 : List Job := [⟨plan7838,[],none,⟨15,15,0⟩⟩]

def t6_1280jobs : List Job := t6_1280jobs0




def t6_1281root : Job := ⟨plan6654,[],none,⟨15,3,0⟩⟩
def t6_1281jobs0 : List Job := [⟨plan6654,[],none,⟨15,3,0⟩⟩]

def t6_1281jobs : List Job := t6_1281jobs0




def t6_1282root : Job := ⟨plan7062,[],none,⟨15,6,0⟩⟩
def t6_1282jobs0 : List Job := [⟨plan7062,[],none,⟨15,6,0⟩⟩]

def t6_1282jobs : List Job := t6_1282jobs0




def t6_1283root : Job := ⟨plan7063,[],none,⟨15,6,0⟩⟩
def t6_1283jobs0 : List Job := [⟨plan7063,[],none,⟨15,6,0⟩⟩]

def t6_1283jobs : List Job := t6_1283jobs0




def t6_1284root : Job := ⟨plan7064,[],none,⟨15,6,0⟩⟩
def t6_1284jobs0 : List Job := [⟨plan7064,[],none,⟨15,6,0⟩⟩]

def t6_1284jobs : List Job := t6_1284jobs0




def t6_1285root : Job := ⟨plan7563,[],none,⟨15,10,0⟩⟩
def t6_1285jobs0 : List Job := [⟨plan7563,[],none,⟨15,10,0⟩⟩]

def t6_1285jobs : List Job := t6_1285jobs0




def t6_1286root : Job := ⟨plan7564,[],none,⟨15,10,0⟩⟩
def t6_1286jobs0 : List Job := [⟨plan7564,[],none,⟨15,10,0⟩⟩]

def t6_1286jobs : List Job := t6_1286jobs0




def t6_1287root : Job := ⟨plan7565,[],none,⟨15,10,0⟩⟩
def t6_1287jobs0 : List Job := [⟨plan7565,[],none,⟨15,10,0⟩⟩]

def t6_1287jobs : List Job := t6_1287jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


