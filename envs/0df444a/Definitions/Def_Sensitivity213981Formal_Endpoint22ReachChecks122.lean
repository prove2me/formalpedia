-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks122
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks122
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:57.078309+00:00
-- url     : https://prove2.me/theorems/084e81f6-c811-431d-8549-a0fc74c7dfa4
-- title:
--   Endpoint22 Reach Checks122 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks122 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1087root`, `ThreeBoundEndpoint22Reachable.t6_1087jobs0`, `ThreeBoundEndpoint22Reachable.t6_1087jobs`, `ThreeBoundEndpoint22Reachable.t6_1088root`, `ThreeBoundEndpoint22Reachable.t6_1088jobs0`, `ThreeBoundEndpoint22Reachable.t6_1088jobs`, `ThreeBoundEndpoint22Reachable.t6_1089root`, `ThreeBoundEndpoint22Reachable.t6_1089jobs0`, `ThreeBoundEndpoint22Reachable.t6_1089jobs`, `ThreeBoundEndpoint22Reachable.t6_1090root`, `ThreeBoundEndpoint22Reachable.t6_1090jobs0`, `ThreeBoundEndpoint22Reachable.t6_1090jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks122.lean, lines 1–860.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
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

def t6_1074root : Job := ⟨plan7504,[],none,⟨15,10,0⟩⟩
def t6_1074jobs0 : List Job := [⟨plan7504,[],none,⟨15,10,0⟩⟩]

def t6_1074jobs : List Job := t6_1074jobs0




def t6_1075root : Job := ⟨plan7505,[],none,⟨15,10,0⟩⟩
def t6_1075jobs0 : List Job := [⟨plan7505,[],none,⟨15,10,0⟩⟩]

def t6_1075jobs : List Job := t6_1075jobs0




def t6_1076root : Job := ⟨plan7741,[],none,⟨15,15,0⟩⟩
def t6_1076jobs0 : List Job := [⟨plan7741,[],none,⟨15,15,0⟩⟩]

def t6_1076jobs : List Job := t6_1076jobs0




def t6_1077root : Job := ⟨plan7742,[],none,⟨15,15,0⟩⟩
def t6_1077jobs0 : List Job := [⟨plan7742,[],none,⟨15,15,0⟩⟩]

def t6_1077jobs : List Job := t6_1077jobs0




def t6_1078root : Job := ⟨plan7743,[],none,⟨15,15,0⟩⟩
def t6_1078jobs0 : List Job := [⟨plan7743,[],none,⟨15,15,0⟩⟩]

def t6_1078jobs : List Job := t6_1078jobs0




def t6_1079root : Job := ⟨plan7744,[],none,⟨15,15,0⟩⟩
def t6_1079jobs0 : List Job := [⟨plan7744,[],none,⟨15,15,0⟩⟩]

def t6_1079jobs : List Job := t6_1079jobs0




def t6_1080root : Job := ⟨plan7745,[],none,⟨15,15,0⟩⟩
def t6_1080jobs0 : List Job := [⟨plan7745,[],none,⟨15,15,0⟩⟩]

def t6_1080jobs : List Job := t6_1080jobs0




def t6_1081root : Job := ⟨plan7746,[],none,⟨15,15,0⟩⟩
def t6_1081jobs0 : List Job := [⟨plan7746,[],none,⟨15,15,0⟩⟩]

def t6_1081jobs : List Job := t6_1081jobs0




def t6_1082root : Job := ⟨plan7747,[],none,⟨15,15,0⟩⟩
def t6_1082jobs0 : List Job := [⟨plan7747,[],none,⟨15,15,0⟩⟩]

def t6_1082jobs : List Job := t6_1082jobs0




def t6_1083root : Job := ⟨plan7748,[],none,⟨15,15,0⟩⟩
def t6_1083jobs0 : List Job := [⟨plan7748,[],none,⟨15,15,0⟩⟩]

def t6_1083jobs : List Job := t6_1083jobs0




def t6_1084root : Job := ⟨plan7749,[],none,⟨15,15,0⟩⟩
def t6_1084jobs0 : List Job := [⟨plan7749,[],none,⟨15,15,0⟩⟩]

def t6_1084jobs : List Job := t6_1084jobs0




def t6_1085root : Job := ⟨plan7750,[],none,⟨15,15,0⟩⟩
def t6_1085jobs0 : List Job := [⟨plan7750,[],none,⟨15,15,0⟩⟩]

def t6_1085jobs : List Job := t6_1085jobs0




def t6_1086root : Job := ⟨plan7751,[],none,⟨15,15,0⟩⟩
def t6_1086jobs0 : List Job := [⟨plan7751,[],none,⟨15,15,0⟩⟩]

def t6_1086jobs : List Job := t6_1086jobs0




def t6_1087root : Job := ⟨plan7752,[],none,⟨15,15,0⟩⟩
def t6_1087jobs0 : List Job := [⟨plan7752,[],none,⟨15,15,0⟩⟩]

def t6_1087jobs : List Job := t6_1087jobs0




def t6_1088root : Job := ⟨plan7753,[],none,⟨15,15,0⟩⟩
def t6_1088jobs0 : List Job := [⟨plan7753,[],none,⟨15,15,0⟩⟩]

def t6_1088jobs : List Job := t6_1088jobs0




def t6_1089root : Job := ⟨plan7754,[],none,⟨15,15,0⟩⟩
def t6_1089jobs0 : List Job := [⟨plan7754,[],none,⟨15,15,0⟩⟩]

def t6_1089jobs : List Job := t6_1089jobs0




def t6_1090root : Job := ⟨plan7755,[],none,⟨15,15,0⟩⟩
def t6_1090jobs0 : List Job := [⟨plan7755,[],none,⟨15,15,0⟩⟩]

def t6_1090jobs : List Job := t6_1090jobs0




def t6_1091root : Job := ⟨plan7756,[],none,⟨15,15,0⟩⟩
def t6_1091jobs0 : List Job := [⟨plan7756,[],none,⟨15,15,0⟩⟩]

def t6_1091jobs : List Job := t6_1091jobs0




def t6_1092root : Job := ⟨plan7757,[],none,⟨15,15,0⟩⟩
def t6_1092jobs0 : List Job := [⟨plan7757,[],none,⟨15,15,0⟩⟩]

def t6_1092jobs : List Job := t6_1092jobs0




def t6_1093root : Job := ⟨plan7758,[],none,⟨15,15,0⟩⟩
def t6_1093jobs0 : List Job := [⟨plan7758,[],none,⟨15,15,0⟩⟩]

def t6_1093jobs : List Job := t6_1093jobs0




def t6_1094root : Job := ⟨plan7759,[],none,⟨15,15,0⟩⟩
def t6_1094jobs0 : List Job := [⟨plan7759,[],none,⟨15,15,0⟩⟩]

def t6_1094jobs : List Job := t6_1094jobs0




def t6_1095root : Job := ⟨plan7760,[],none,⟨15,15,0⟩⟩
def t6_1095jobs0 : List Job := [⟨plan7760,[],none,⟨15,15,0⟩⟩]

def t6_1095jobs : List Job := t6_1095jobs0




def t6_1096root : Job := ⟨plan7761,[],none,⟨15,15,0⟩⟩
def t6_1096jobs0 : List Job := [⟨plan7761,[],none,⟨15,15,0⟩⟩]

def t6_1096jobs : List Job := t6_1096jobs0




def t6_1097root : Job := ⟨plan7762,[],none,⟨15,15,0⟩⟩
def t6_1097jobs0 : List Job := [⟨plan7762,[],none,⟨15,15,0⟩⟩]

def t6_1097jobs : List Job := t6_1097jobs0




def t6_1098root : Job := ⟨plan7763,[],none,⟨15,15,0⟩⟩
def t6_1098jobs0 : List Job := [⟨plan7763,[],none,⟨15,15,0⟩⟩]

def t6_1098jobs : List Job := t6_1098jobs0




def t6_1099root : Job := ⟨plan7764,[],none,⟨15,15,0⟩⟩
def t6_1099jobs0 : List Job := [⟨plan7764,[],none,⟨15,15,0⟩⟩]

def t6_1099jobs : List Job := t6_1099jobs0




def t6_1100root : Job := ⟨plan7765,[],none,⟨15,15,0⟩⟩
def t6_1100jobs0 : List Job := [⟨plan7765,[],none,⟨15,15,0⟩⟩]

def t6_1100jobs : List Job := t6_1100jobs0




def t6_1101root : Job := ⟨plan7766,[],none,⟨15,15,0⟩⟩
def t6_1101jobs0 : List Job := [⟨plan7766,[],none,⟨15,15,0⟩⟩]

def t6_1101jobs : List Job := t6_1101jobs0




def t6_1102root : Job := ⟨plan7767,[],none,⟨15,15,0⟩⟩
def t6_1102jobs0 : List Job := [⟨plan7767,[],none,⟨15,15,0⟩⟩]

def t6_1102jobs : List Job := t6_1102jobs0




def t6_1103root : Job := ⟨plan7032,[],none,⟨15,6,0⟩⟩
def t6_1103jobs0 : List Job := [⟨plan7032,[],none,⟨15,6,0⟩⟩]

def t6_1103jobs : List Job := t6_1103jobs0




def t6_1104root : Job := ⟨plan7506,[],none,⟨15,10,0⟩⟩
def t6_1104jobs0 : List Job := [⟨plan7506,[],none,⟨15,10,0⟩⟩]

def t6_1104jobs : List Job := t6_1104jobs0




def t6_1105root : Job := ⟨plan7507,[],none,⟨15,10,0⟩⟩
def t6_1105jobs0 : List Job := [⟨plan7507,[],none,⟨15,10,0⟩⟩]

def t6_1105jobs : List Job := t6_1105jobs0




def t6_1106root : Job := ⟨plan7508,[],none,⟨15,10,0⟩⟩
def t6_1106jobs0 : List Job := [⟨plan7508,[],none,⟨15,10,0⟩⟩]

def t6_1106jobs : List Job := t6_1106jobs0




def t6_1107root : Job := ⟨plan6640,[],none,⟨15,3,0⟩⟩
def t6_1107jobs0 : List Job := [⟨plan6640,[],none,⟨15,3,0⟩⟩]

def t6_1107jobs : List Job := t6_1107jobs0




def t6_1108root : Job := ⟨plan7033,[],none,⟨15,6,0⟩⟩
def t6_1108jobs0 : List Job := [⟨plan7033,[],none,⟨15,6,0⟩⟩]

def t6_1108jobs : List Job := t6_1108jobs0




def t6_1109root : Job := ⟨plan7034,[],none,⟨15,6,0⟩⟩
def t6_1109jobs0 : List Job := [⟨plan7034,[],none,⟨15,6,0⟩⟩]

def t6_1109jobs : List Job := t6_1109jobs0




def t6_1110root : Job := ⟨plan7035,[],none,⟨15,6,0⟩⟩
def t6_1110jobs0 : List Job := [⟨plan7035,[],none,⟨15,6,0⟩⟩]

def t6_1110jobs : List Job := t6_1110jobs0




def t6_1111root : Job := ⟨plan7509,[],none,⟨15,10,0⟩⟩
def t6_1111jobs0 : List Job := [⟨plan7509,[],none,⟨15,10,0⟩⟩]

def t6_1111jobs : List Job := t6_1111jobs0




def t6_1112root : Job := ⟨plan7510,[],none,⟨15,10,0⟩⟩
def t6_1112jobs0 : List Job := [⟨plan7510,[],none,⟨15,10,0⟩⟩]

def t6_1112jobs : List Job := t6_1112jobs0




def t6_1113root : Job := ⟨plan7511,[],none,⟨15,10,0⟩⟩
def t6_1113jobs0 : List Job := [⟨plan7511,[],none,⟨15,10,0⟩⟩]

def t6_1113jobs : List Job := t6_1113jobs0




def t6_1114root : Job := ⟨plan7512,[],none,⟨15,10,0⟩⟩
def t6_1114jobs0 : List Job := [⟨plan7512,[],none,⟨15,10,0⟩⟩]

def t6_1114jobs : List Job := t6_1114jobs0




def t6_1115root : Job := ⟨plan7513,[],none,⟨15,10,0⟩⟩
def t6_1115jobs0 : List Job := [⟨plan7513,[],none,⟨15,10,0⟩⟩]

def t6_1115jobs : List Job := t6_1115jobs0




def t6_1116root : Job := ⟨plan7514,[],none,⟨15,10,0⟩⟩
def t6_1116jobs0 : List Job := [⟨plan7514,[],none,⟨15,10,0⟩⟩]

def t6_1116jobs : List Job := t6_1116jobs0




def t6_1117root : Job := ⟨plan7515,[],none,⟨15,10,0⟩⟩
def t6_1117jobs0 : List Job := [⟨plan7515,[],none,⟨15,10,0⟩⟩]

def t6_1117jobs : List Job := t6_1117jobs0




def t6_1118root : Job := ⟨plan7768,[],none,⟨15,15,0⟩⟩
def t6_1118jobs0 : List Job := [⟨plan7768,[],none,⟨15,15,0⟩⟩]

def t6_1118jobs : List Job := t6_1118jobs0




def t6_1119root : Job := ⟨plan7769,[],none,⟨15,15,0⟩⟩
def t6_1119jobs0 : List Job := [⟨plan7769,[],none,⟨15,15,0⟩⟩]

def t6_1119jobs : List Job := t6_1119jobs0




def t6_1120root : Job := ⟨plan7770,[],none,⟨15,15,0⟩⟩
def t6_1120jobs0 : List Job := [⟨plan7770,[],none,⟨15,15,0⟩⟩]

def t6_1120jobs : List Job := t6_1120jobs0




def t6_1121root : Job := ⟨plan7771,[],none,⟨15,15,0⟩⟩
def t6_1121jobs0 : List Job := [⟨plan7771,[],none,⟨15,15,0⟩⟩]

def t6_1121jobs : List Job := t6_1121jobs0




def t6_1122root : Job := ⟨plan7772,[],none,⟨15,15,0⟩⟩
def t6_1122jobs0 : List Job := [⟨plan7772,[],none,⟨15,15,0⟩⟩]

def t6_1122jobs : List Job := t6_1122jobs0




def t6_1123root : Job := ⟨plan7773,[],none,⟨15,15,0⟩⟩
def t6_1123jobs0 : List Job := [⟨plan7773,[],none,⟨15,15,0⟩⟩]

def t6_1123jobs : List Job := t6_1123jobs0




def t6_1124root : Job := ⟨plan7774,[],none,⟨15,15,0⟩⟩
def t6_1124jobs0 : List Job := [⟨plan7774,[],none,⟨15,15,0⟩⟩]

def t6_1124jobs : List Job := t6_1124jobs0




def t6_1125root : Job := ⟨plan7775,[],none,⟨15,15,0⟩⟩
def t6_1125jobs0 : List Job := [⟨plan7775,[],none,⟨15,15,0⟩⟩]

def t6_1125jobs : List Job := t6_1125jobs0




def t6_1126root : Job := ⟨plan7776,[],none,⟨15,15,0⟩⟩
def t6_1126jobs0 : List Job := [⟨plan7776,[],none,⟨15,15,0⟩⟩]

def t6_1126jobs : List Job := t6_1126jobs0




def t6_1127root : Job := ⟨plan7777,[],none,⟨15,15,0⟩⟩
def t6_1127jobs0 : List Job := [⟨plan7777,[],none,⟨15,15,0⟩⟩]

def t6_1127jobs : List Job := t6_1127jobs0




def t6_1128root : Job := ⟨plan7778,[],none,⟨15,15,0⟩⟩
def t6_1128jobs0 : List Job := [⟨plan7778,[],none,⟨15,15,0⟩⟩]

def t6_1128jobs : List Job := t6_1128jobs0




def t6_1129root : Job := ⟨plan7516,[],none,⟨15,10,0⟩⟩
def t6_1129jobs0 : List Job := [⟨plan7516,[],none,⟨15,10,0⟩⟩]

def t6_1129jobs : List Job := t6_1129jobs0




def t6_1130root : Job := ⟨plan7779,[],none,⟨15,15,0⟩⟩
def t6_1130jobs0 : List Job := [⟨plan7779,[],none,⟨15,15,0⟩⟩]

def t6_1130jobs : List Job := t6_1130jobs0




def t6_1131root : Job := ⟨plan7780,[],none,⟨15,15,0⟩⟩
def t6_1131jobs0 : List Job := [⟨plan7780,[],none,⟨15,15,0⟩⟩]

def t6_1131jobs : List Job := t6_1131jobs0




def t6_1132root : Job := ⟨plan7781,[],none,⟨15,15,0⟩⟩
def t6_1132jobs0 : List Job := [⟨plan7781,[],none,⟨15,15,0⟩⟩]

def t6_1132jobs : List Job := t6_1132jobs0




def t6_1133root : Job := ⟨plan7782,[],none,⟨15,15,0⟩⟩
def t6_1133jobs0 : List Job := [⟨plan7782,[],none,⟨15,15,0⟩⟩]

def t6_1133jobs : List Job := t6_1133jobs0




def t6_1134root : Job := ⟨plan7783,[],none,⟨15,15,0⟩⟩
def t6_1134jobs0 : List Job := [⟨plan7783,[],none,⟨15,15,0⟩⟩]

def t6_1134jobs : List Job := t6_1134jobs0




def t6_1135root : Job := ⟨plan7784,[],none,⟨15,15,0⟩⟩
def t6_1135jobs0 : List Job := [⟨plan7784,[],none,⟨15,15,0⟩⟩]

def t6_1135jobs : List Job := t6_1135jobs0




def t6_1136root : Job := ⟨plan6415,[],none,⟨15,1,0⟩⟩
def t6_1136jobs0 : List Job := [⟨plan6415,[],none,⟨15,1,0⟩⟩]

def t6_1136jobs : List Job := t6_1136jobs0




def t6_1137root : Job := ⟨plan6641,[],none,⟨15,3,0⟩⟩
def t6_1137jobs0 : List Job := [⟨plan6641,[],none,⟨15,3,0⟩⟩]

def t6_1137jobs : List Job := t6_1137jobs0




def t6_1138root : Job := ⟨plan6642,[],none,⟨15,3,0⟩⟩
def t6_1138jobs0 : List Job := [⟨plan6642,[],none,⟨15,3,0⟩⟩]

def t6_1138jobs : List Job := t6_1138jobs0




def t6_1139root : Job := ⟨plan6643,[],none,⟨15,3,0⟩⟩
def t6_1139jobs0 : List Job := [⟨plan6643,[],none,⟨15,3,0⟩⟩]

def t6_1139jobs : List Job := t6_1139jobs0




def t6_1140root : Job := ⟨plan7036,[],none,⟨15,6,0⟩⟩
def t6_1140jobs0 : List Job := [⟨plan7036,[],none,⟨15,6,0⟩⟩]

def t6_1140jobs : List Job := t6_1140jobs0




def t6_1141root : Job := ⟨plan7037,[],none,⟨15,6,0⟩⟩
def t6_1141jobs0 : List Job := [⟨plan5715,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5715,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1141jobs1 : List Job := [⟨plan5715,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1141jobs : List Job := t6_1141jobs0++t6_1141jobs1




def t6_1142root : Job := ⟨plan7038,[],none,⟨15,6,0⟩⟩
def t6_1142jobs0 : List Job := [⟨plan7038,[],none,⟨15,6,0⟩⟩]

def t6_1142jobs : List Job := t6_1142jobs0




def t6_1143root : Job := ⟨plan7039,[],none,⟨15,6,0⟩⟩
def t6_1143jobs0 : List Job := [⟨plan5717,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5717,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1143jobs1 : List Job := [⟨plan5717,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1143jobs : List Job := t6_1143jobs0++t6_1143jobs1




def t6_1144root : Job := ⟨plan7040,[],none,⟨15,6,0⟩⟩
def t6_1144jobs0 : List Job := [⟨plan5718,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5718,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1144jobs1 : List Job := [⟨plan5718,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1144jobs : List Job := t6_1144jobs0++t6_1144jobs1




def t6_1145root : Job := ⟨plan7041,[],none,⟨15,6,0⟩⟩
def t6_1145jobs0 : List Job := [⟨plan7041,[],none,⟨15,6,0⟩⟩]

def t6_1145jobs : List Job := t6_1145jobs0




def t6_1146root : Job := ⟨plan7517,[],none,⟨15,10,0⟩⟩
def t6_1146jobs0 : List Job := [⟨plan7517,[],none,⟨15,10,0⟩⟩]

def t6_1146jobs : List Job := t6_1146jobs0




def t6_1147root : Job := ⟨plan7518,[],none,⟨15,10,0⟩⟩
def t6_1147jobs0 : List Job := [⟨plan7518,[],none,⟨15,10,0⟩⟩]

def t6_1147jobs : List Job := t6_1147jobs0




def t6_1148root : Job := ⟨plan7519,[],none,⟨15,10,0⟩⟩
def t6_1148jobs0 : List Job := [⟨plan7519,[],none,⟨15,10,0⟩⟩]

def t6_1148jobs : List Job := t6_1148jobs0




def t6_1149root : Job := ⟨plan7520,[],none,⟨15,10,0⟩⟩
def t6_1149jobs0 : List Job := [⟨plan5930,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5930,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1149jobs1 : List Job := [⟨plan5930,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1149jobs : List Job := t6_1149jobs0++t6_1149jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


