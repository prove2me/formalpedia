-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans094
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans094
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:08:25.190125+00:00
-- url     : https://prove2.me/theorems/fcb08db2-a133-417c-ae18-c0e283b322a9
-- title:
--   Endpoint22 Reach Plans094 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans094 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan9093`, `ThreeBoundEndpoint22Reachable.plan9094`, `ThreeBoundEndpoint22Reachable.plan9095`, `ThreeBoundEndpoint22Reachable.plan9096`, `ThreeBoundEndpoint22Reachable.plan9097`, `ThreeBoundEndpoint22Reachable.plan9098`, `ThreeBoundEndpoint22Reachable.plan9030`, `ThreeBoundEndpoint22Reachable.plan9099`, `ThreeBoundEndpoint22Reachable.plan9100`, `ThreeBoundEndpoint22Reachable.plan9101`, `ThreeBoundEndpoint22Reachable.plan9102`, `ThreeBoundEndpoint22Reachable.plan9103`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans094.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
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
def plan9025 : Plan := .step choices290 bits1800 plan8383

def plan9026 : Plan := .step choices290 bits1799 plan8384

def plan9027 : Plan := .step choices290 bits1798 plan8385

def plan9028 : Plan := .step choices290 bits1797 plan8386

def plan9029 : Plan := .step choices291 bits1797 plan8344

def plan9030 : Plan := .step choices291 bits1798 plan8345

def plan9031 : Plan := .step choices291 bits1797 plan8346

def plan9032 : Plan := .step choices291 bits1799 plan8347

def plan9033 : Plan := .step choices291 bits1798 plan8348

def plan9034 : Plan := .step choices291 bits1797 plan8349

def plan9035 : Plan := .step choices291 bits1800 plan8350

def plan9036 : Plan := .step choices291 bits1799 plan8351

def plan9037 : Plan := .step choices291 bits1798 plan8352

def plan9038 : Plan := .step choices291 bits1797 plan8353

def plan9039 : Plan := .step choices291 bits1801 plan8354

def plan9040 : Plan := .step choices291 bits1800 plan8355

def plan9041 : Plan := .step choices291 bits1799 plan8356

def plan9042 : Plan := .step choices291 bits1798 plan8357

def plan9043 : Plan := .step choices291 bits1797 plan8358

def plan9044 : Plan := .step choices291 bits1802 plan8359

def plan9045 : Plan := .step choices291 bits1801 plan8360

def plan9046 : Plan := .step choices291 bits1800 plan8361

def plan9047 : Plan := .step choices291 bits1799 plan8362

def plan9048 : Plan := .step choices291 bits1798 plan8363

def plan9049 : Plan := .step choices291 bits1797 plan8364

def plan9050 : Plan := .step choices291 bits1803 plan8365

def plan9051 : Plan := .step choices291 bits1802 plan8382

def plan9052 : Plan := .step choices291 bits1801 plan8383

def plan9053 : Plan := .step choices291 bits1800 plan8384

def plan9054 : Plan := .step choices291 bits1799 plan8385

def plan9055 : Plan := .step choices291 bits1798 plan8386

def plan9056 : Plan := .step choices291 bits1797 plan8387

def plan9057 : Plan := .step choices292 bits1804 plan8365

def plan9058 : Plan := .step choices293 bits1797 plan8329

def plan9059 : Plan := .step choices293 bits1797 plan8332

def plan9060 : Plan := .step choices293 bits1798 plan8334

def plan9061 : Plan := .step choices293 bits1797 plan8335

def plan9062 : Plan := .step choices293 bits1799 plan8337

def plan9063 : Plan := .step choices293 bits1797 plan8339

def plan9064 : Plan := .step choices293 bits1798 plan8341

def plan9065 : Plan := .step choices293 bits1797 plan8342

def plan9066 : Plan := .step choices293 bits1797 plan8347

def plan9067 : Plan := .step choices293 bits1798 plan8350

def plan9068 : Plan := .step choices293 bits1797 plan8351

def plan9069 : Plan := .step choices293 bits1799 plan8354

def plan9070 : Plan := .step choices293 bits1798 plan8355

def plan9071 : Plan := .step choices293 bits1797 plan8356

def plan9072 : Plan := .step choices293 bits1800 plan8359

def plan9073 : Plan := .step choices293 bits1799 plan8360

def plan9074 : Plan := .step choices293 bits1798 plan8361

def plan9075 : Plan := .step choices293 bits1797 plan8362

def plan9076 : Plan := .step choices293 bits1801 plan8365

def plan9077 : Plan := .step choices293 bits1797 plan8366

def plan9078 : Plan := .step choices293 bits1798 plan8367

def plan9079 : Plan := .step choices293 bits1797 plan8368

def plan9080 : Plan := .step choices293 bits1797 plan8370

def plan9081 : Plan := .step choices293 bits1798 plan8372

def plan9082 : Plan := .step choices293 bits1797 plan8373

def plan9083 : Plan := .step choices293 bits1799 plan8375

def plan9084 : Plan := .step choices293 bits1797 plan8377

def plan9085 : Plan := .step choices293 bits1798 plan8379

def plan9086 : Plan := .step choices293 bits1797 plan8380

def plan9087 : Plan := .step choices293 bits1800 plan8382

def plan9088 : Plan := .step choices293 bits1799 plan8383

def plan9089 : Plan := .step choices293 bits1798 plan8384

def plan9090 : Plan := .step choices293 bits1797 plan8385

def plan9091 : Plan := .step choices294 bits1797 plan8345

def plan9092 : Plan := .step choices294 bits1798 plan8347

def plan9093 : Plan := .step choices294 bits1797 plan8348

def plan9094 : Plan := .step choices294 bits1799 plan8350

def plan9095 : Plan := .step choices294 bits1798 plan8351

def plan9096 : Plan := .step choices294 bits1797 plan8352

def plan9097 : Plan := .step choices294 bits1800 plan8354

def plan9098 : Plan := .step choices294 bits1799 plan8355

def plan9099 : Plan := .step choices294 bits1798 plan8356

def plan9100 : Plan := .step choices294 bits1797 plan8357

def plan9101 : Plan := .step choices294 bits1801 plan8359

def plan9102 : Plan := .step choices294 bits1800 plan8360

def plan9103 : Plan := .step choices294 bits1799 plan8361

def plan9104 : Plan := .step choices294 bits1798 plan8362

def plan9105 : Plan := .step choices294 bits1797 plan8363

def plan9106 : Plan := .step choices294 bits1802 plan8365

def plan9107 : Plan := .step choices294 bits1797 plan8369

def plan9108 : Plan := .step choices294 bits1798 plan8370

def plan9109 : Plan := .step choices294 bits1797 plan8371

def plan9110 : Plan := .step choices294 bits1799 plan8372

def plan9111 : Plan := .step choices294 bits1798 plan8373

def plan9112 : Plan := .step choices294 bits1797 plan8374

def plan9113 : Plan := .step choices294 bits1800 plan8375

def plan9114 : Plan := .step choices294 bits1797 plan8376

def plan9115 : Plan := .step choices294 bits1798 plan8377

def plan9116 : Plan := .step choices294 bits1797 plan8378

def plan9117 : Plan := .step choices294 bits1799 plan8379

def plan9118 : Plan := .step choices294 bits1798 plan8380

def plan9119 : Plan := .step choices294 bits1797 plan8381

def plan9120 : Plan := .step choices294 bits1801 plan8382

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


