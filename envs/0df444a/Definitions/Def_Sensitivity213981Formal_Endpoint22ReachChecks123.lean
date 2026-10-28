-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks123
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks123
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:53.749902+00:00
-- url     : https://prove2.me/theorems/c2471529-3b7f-46b7-ab68-9761159e1261
-- title:
--   Endpoint22 Reach Checks123 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks123 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1162root`, `ThreeBoundEndpoint22Reachable.t6_1162jobs0`, `ThreeBoundEndpoint22Reachable.t6_1162jobs`, `ThreeBoundEndpoint22Reachable.t6_1163root`, `ThreeBoundEndpoint22Reachable.t6_1163jobs0`, `ThreeBoundEndpoint22Reachable.t6_1163jobs`, `ThreeBoundEndpoint22Reachable.t6_1164root`, `ThreeBoundEndpoint22Reachable.t6_1164jobs0`, `ThreeBoundEndpoint22Reachable.t6_1164jobs`, `ThreeBoundEndpoint22Reachable.t6_1165root`, `ThreeBoundEndpoint22Reachable.t6_1165jobs0`, `ThreeBoundEndpoint22Reachable.t6_1165jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks123.lean, lines 1–488.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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

def t6_1150root : Job := ⟨plan7521,[],none,⟨15,10,0⟩⟩
def t6_1150jobs0 : List Job := [⟨plan7521,[],none,⟨15,10,0⟩⟩]

def t6_1150jobs : List Job := t6_1150jobs0




def t6_1151root : Job := ⟨plan7522,[],none,⟨15,10,0⟩⟩
def t6_1151jobs0 : List Job := [⟨plan7522,[],none,⟨15,10,0⟩⟩]

def t6_1151jobs : List Job := t6_1151jobs0




def t6_1152root : Job := ⟨plan7523,[],none,⟨15,10,0⟩⟩
def t6_1152jobs0 : List Job := [⟨plan5933,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5933,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1152jobs1 : List Job := [⟨plan5933,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1152jobs : List Job := t6_1152jobs0++t6_1152jobs1




def t6_1153root : Job := ⟨plan7524,[],none,⟨15,10,0⟩⟩
def t6_1153jobs0 : List Job := [⟨plan5934,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5934,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1153jobs1 : List Job := [⟨plan5934,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1153jobs : List Job := t6_1153jobs0++t6_1153jobs1




def t6_1154root : Job := ⟨plan7525,[],none,⟨15,10,0⟩⟩
def t6_1154jobs0 : List Job := [⟨plan7525,[],none,⟨15,10,0⟩⟩]

def t6_1154jobs : List Job := t6_1154jobs0




def t6_1155root : Job := ⟨plan7526,[],none,⟨15,10,0⟩⟩
def t6_1155jobs0 : List Job := [⟨plan7526,[],none,⟨15,10,0⟩⟩]

def t6_1155jobs : List Job := t6_1155jobs0




def t6_1156root : Job := ⟨plan7785,[],none,⟨15,15,0⟩⟩
def t6_1156jobs0 : List Job := [⟨plan7785,[],none,⟨15,15,0⟩⟩]

def t6_1156jobs : List Job := t6_1156jobs0




def t6_1157root : Job := ⟨plan7786,[],none,⟨15,15,0⟩⟩
def t6_1157jobs0 : List Job := [⟨plan7786,[],none,⟨15,15,0⟩⟩]

def t6_1157jobs : List Job := t6_1157jobs0




def t6_1158root : Job := ⟨plan7787,[],none,⟨15,15,0⟩⟩
def t6_1158jobs0 : List Job := [⟨plan7787,[],none,⟨15,15,0⟩⟩]

def t6_1158jobs : List Job := t6_1158jobs0




def t6_1159root : Job := ⟨plan7788,[],none,⟨15,15,0⟩⟩
def t6_1159jobs0 : List Job := [⟨plan7788,[],none,⟨15,15,0⟩⟩]

def t6_1159jobs : List Job := t6_1159jobs0




def t6_1160root : Job := ⟨plan7789,[],none,⟨15,15,0⟩⟩
def t6_1160jobs0 : List Job := [⟨plan7789,[],none,⟨15,15,0⟩⟩]

def t6_1160jobs : List Job := t6_1160jobs0




def t6_1161root : Job := ⟨plan7790,[],none,⟨15,15,0⟩⟩
def t6_1161jobs0 : List Job := [⟨plan7790,[],none,⟨15,15,0⟩⟩]

def t6_1161jobs : List Job := t6_1161jobs0




def t6_1162root : Job := ⟨plan7791,[],none,⟨15,15,0⟩⟩
def t6_1162jobs0 : List Job := [⟨plan7791,[],none,⟨15,15,0⟩⟩]

def t6_1162jobs : List Job := t6_1162jobs0




def t6_1163root : Job := ⟨plan7792,[],none,⟨15,15,0⟩⟩
def t6_1163jobs0 : List Job := [⟨plan7792,[],none,⟨15,15,0⟩⟩]

def t6_1163jobs : List Job := t6_1163jobs0




def t6_1164root : Job := ⟨plan7793,[],none,⟨15,15,0⟩⟩
def t6_1164jobs0 : List Job := [⟨plan7793,[],none,⟨15,15,0⟩⟩]

def t6_1164jobs : List Job := t6_1164jobs0




def t6_1165root : Job := ⟨plan7794,[],none,⟨15,15,0⟩⟩
def t6_1165jobs0 : List Job := [⟨plan7794,[],none,⟨15,15,0⟩⟩]

def t6_1165jobs : List Job := t6_1165jobs0




def t6_1166root : Job := ⟨plan7795,[],none,⟨15,15,0⟩⟩
def t6_1166jobs0 : List Job := [⟨plan7795,[],none,⟨15,15,0⟩⟩]

def t6_1166jobs : List Job := t6_1166jobs0




def t6_1167root : Job := ⟨plan7042,[],none,⟨15,6,0⟩⟩
def t6_1167jobs0 : List Job := [⟨plan7042,[],none,⟨15,6,0⟩⟩]

def t6_1167jobs : List Job := t6_1167jobs0




def t6_1168root : Job := ⟨plan7527,[],none,⟨15,10,0⟩⟩
def t6_1168jobs0 : List Job := [⟨plan7527,[],none,⟨15,10,0⟩⟩]

def t6_1168jobs : List Job := t6_1168jobs0




def t6_1169root : Job := ⟨plan7528,[],none,⟨15,10,0⟩⟩
def t6_1169jobs0 : List Job := [⟨plan7528,[],none,⟨15,10,0⟩⟩]

def t6_1169jobs : List Job := t6_1169jobs0




def t6_1170root : Job := ⟨plan7529,[],none,⟨15,10,0⟩⟩
def t6_1170jobs0 : List Job := [⟨plan7529,[],none,⟨15,10,0⟩⟩]

def t6_1170jobs : List Job := t6_1170jobs0




def t6_1171root : Job := ⟨plan7796,[],none,⟨15,15,0⟩⟩
def t6_1171jobs0 : List Job := [⟨plan7796,[],none,⟨15,15,0⟩⟩]

def t6_1171jobs : List Job := t6_1171jobs0




def t6_1172root : Job := ⟨plan7797,[],none,⟨15,15,0⟩⟩
def t6_1172jobs0 : List Job := [⟨plan7797,[],none,⟨15,15,0⟩⟩]

def t6_1172jobs : List Job := t6_1172jobs0




def t6_1173root : Job := ⟨plan7798,[],none,⟨15,15,0⟩⟩
def t6_1173jobs0 : List Job := [⟨plan7798,[],none,⟨15,15,0⟩⟩]

def t6_1173jobs : List Job := t6_1173jobs0




def t6_1174root : Job := ⟨plan7799,[],none,⟨15,15,0⟩⟩
def t6_1174jobs0 : List Job := [⟨plan7799,[],none,⟨15,15,0⟩⟩]

def t6_1174jobs : List Job := t6_1174jobs0




def t6_1175root : Job := ⟨plan7800,[],none,⟨15,15,0⟩⟩
def t6_1175jobs0 : List Job := [⟨plan7800,[],none,⟨15,15,0⟩⟩]

def t6_1175jobs : List Job := t6_1175jobs0




def t6_1176root : Job := ⟨plan7801,[],none,⟨15,15,0⟩⟩
def t6_1176jobs0 : List Job := [⟨plan7801,[],none,⟨15,15,0⟩⟩]

def t6_1176jobs : List Job := t6_1176jobs0




def t6_1177root : Job := ⟨plan7802,[],none,⟨15,15,0⟩⟩
def t6_1177jobs0 : List Job := [⟨plan7802,[],none,⟨15,15,0⟩⟩]

def t6_1177jobs : List Job := t6_1177jobs0




def t6_1178root : Job := ⟨plan7803,[],none,⟨15,15,0⟩⟩
def t6_1178jobs0 : List Job := [⟨plan7803,[],none,⟨15,15,0⟩⟩]

def t6_1178jobs : List Job := t6_1178jobs0




def t6_1179root : Job := ⟨plan7804,[],none,⟨15,15,0⟩⟩
def t6_1179jobs0 : List Job := [⟨plan7804,[],none,⟨15,15,0⟩⟩]

def t6_1179jobs : List Job := t6_1179jobs0




def t6_1180root : Job := ⟨plan7805,[],none,⟨15,15,0⟩⟩
def t6_1180jobs0 : List Job := [⟨plan7805,[],none,⟨15,15,0⟩⟩]

def t6_1180jobs : List Job := t6_1180jobs0




def t6_1181root : Job := ⟨plan7806,[],none,⟨15,15,0⟩⟩
def t6_1181jobs0 : List Job := [⟨plan7806,[],none,⟨15,15,0⟩⟩]

def t6_1181jobs : List Job := t6_1181jobs0




def t6_1182root : Job := ⟨plan7807,[],none,⟨15,15,0⟩⟩
def t6_1182jobs0 : List Job := [⟨plan7807,[],none,⟨15,15,0⟩⟩]

def t6_1182jobs : List Job := t6_1182jobs0




def t6_1183root : Job := ⟨plan7808,[],none,⟨15,15,0⟩⟩
def t6_1183jobs0 : List Job := [⟨plan7808,[],none,⟨15,15,0⟩⟩]

def t6_1183jobs : List Job := t6_1183jobs0




def t6_1184root : Job := ⟨plan7809,[],none,⟨15,15,0⟩⟩
def t6_1184jobs0 : List Job := [⟨plan7809,[],none,⟨15,15,0⟩⟩]

def t6_1184jobs : List Job := t6_1184jobs0




def t6_1185root : Job := ⟨plan7810,[],none,⟨15,15,0⟩⟩
def t6_1185jobs0 : List Job := [⟨plan7810,[],none,⟨15,15,0⟩⟩]

def t6_1185jobs : List Job := t6_1185jobs0




def t6_1186root : Job := ⟨plan7811,[],none,⟨15,15,0⟩⟩
def t6_1186jobs0 : List Job := [⟨plan7811,[],none,⟨15,15,0⟩⟩]

def t6_1186jobs : List Job := t6_1186jobs0




def t6_1187root : Job := ⟨plan6316,[],none,⟨15,0,0⟩⟩
def t6_1187jobs0 : List Job := [⟨plan6316,[],none,⟨15,0,0⟩⟩]

def t6_1187jobs : List Job := t6_1187jobs0




def t6_1188root : Job := ⟨plan6416,[],none,⟨15,1,0⟩⟩
def t6_1188jobs0 : List Job := [⟨plan6416,[],none,⟨15,1,0⟩⟩]

def t6_1188jobs : List Job := t6_1188jobs0




def t6_1189root : Job := ⟨plan6417,[],none,⟨15,1,0⟩⟩
def t6_1189jobs0 : List Job := [⟨plan5394,[⟨5,0,1⟩],(some ⟨5,0,1⟩),⟨15,0,(-1)⟩⟩,⟨plan5394,[⟨5,1,0⟩],(some ⟨5,1,0⟩),⟨14,1,1⟩⟩,⟨plan5394,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,0,0⟩⟩]

def t6_1189jobs1 : List Job := [⟨plan5394,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,1,2⟩⟩]

def t6_1189jobs2 : List Job := [⟨plan5394,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,0,1⟩⟩]

def t6_1189jobs : List Job := t6_1189jobs0++t6_1189jobs1++t6_1189jobs2




def t6_1190root : Job := ⟨plan6418,[],none,⟨15,1,0⟩⟩
def t6_1190jobs0 : List Job := [⟨plan6418,[],none,⟨15,1,0⟩⟩]

def t6_1190jobs : List Job := t6_1190jobs0




def t6_1191root : Job := ⟨plan6644,[],none,⟨15,3,0⟩⟩
def t6_1191jobs0 : List Job := [⟨plan5480,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5480,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,0⟩⟩,⟨plan5480,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-1)⟩⟩,⟨plan5480,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,2⟩⟩]

def t6_1191jobs1 : List Job := [⟨plan5480,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,1⟩⟩,⟨plan5480,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,0⟩⟩]

def t6_1191jobs : List Job := t6_1191jobs0++t6_1191jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


