-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans010
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:56.852109+00:00
-- url     : https://prove2.me/theorems/8115650c-e209-4848-b394-c712df3bbcc1
-- title:
--   Endpoint22 Reach Plans010 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans010 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1031`, `ThreeBoundEndpoint22Reachable.plan1032`, `ThreeBoundEndpoint22Reachable.plan1033`, `ThreeBoundEndpoint22Reachable.plan1034`, `ThreeBoundEndpoint22Reachable.plan1035`, `ThreeBoundEndpoint22Reachable.plan1036`, `ThreeBoundEndpoint22Reachable.plan1037`, `ThreeBoundEndpoint22Reachable.plan1038`, `ThreeBoundEndpoint22Reachable.plan966`, `ThreeBoundEndpoint22Reachable.plan1039`, `ThreeBoundEndpoint22Reachable.plan1040`, `ThreeBoundEndpoint22Reachable.plan1041`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans010.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
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
def plan961 : Plan := .step choices82 bits245 plan377

def plan962 : Plan := .step choices82 bits245 plan378

def plan963 : Plan := .step choices82 bits241 plan380

def plan964 : Plan := .step choices82 bits241 plan381

def plan965 : Plan := .step choices82 bits241 plan382

def plan966 : Plan := .step choices82 bits244 plan384

def plan967 : Plan := .step choices82 bits244 plan385

def plan968 : Plan := .step choices82 bits243 plan386

def plan969 : Plan := .step choices82 bits244 plan387

def plan970 : Plan := .step choices82 bits245 plan388

def plan971 : Plan := .step choices82 bits245 plan389

def plan972 : Plan := .step choices83 bits288 plan356

def plan973 : Plan := .step choices83 bits289 plan357

def plan974 : Plan := .step choices83 bits289 plan358

def plan975 : Plan := .step choices83 bits288 plan359

def plan976 : Plan := .step choices83 bits289 plan360

def plan977 : Plan := .step choices83 bits292 plan362

def plan978 : Plan := .step choices83 bits292 plan363

def plan979 : Plan := .step choices83 bits292 plan364

def plan980 : Plan := .step choices83 bits291 plan369

def plan981 : Plan := .step choices83 bits248 plan370

def plan982 : Plan := .step choices83 bits249 plan371

def plan983 : Plan := .step choices83 bits249 plan372

def plan984 : Plan := .step choices83 bits248 plan373

def plan985 : Plan := .step choices83 bits249 plan374

def plan986 : Plan := .step choices83 bits250 plan375

def plan987 : Plan := .step choices83 bits250 plan376

def plan988 : Plan := .step choices83 bits250 plan377

def plan989 : Plan := .step choices83 bits250 plan378

def plan990 : Plan := .step choices83 bits291 plan383

def plan991 : Plan := .step choices83 bits249 plan384

def plan992 : Plan := .step choices83 bits249 plan385

def plan993 : Plan := .step choices83 bits248 plan386

def plan994 : Plan := .step choices83 bits249 plan387

def plan995 : Plan := .step choices83 bits250 plan388

def plan996 : Plan := .step choices83 bits250 plan389

def plan997 : Plan := .step choices84 bits294 plan362

def plan998 : Plan := .step choices84 bits294 plan363

def plan999 : Plan := .step choices84 bits294 plan364

def plan1000 : Plan := .step choices84 bits253 plan375

def plan1001 : Plan := .step choices84 bits253 plan376

def plan1002 : Plan := .step choices84 bits253 plan377

def plan1003 : Plan := .step choices84 bits253 plan378

def plan1004 : Plan := .step choices84 bits253 plan388

def plan1005 : Plan := .step choices84 bits253 plan389

def plan1006 : Plan := .step choices85 bits286 plan354

def plan1007 : Plan := .step choices85 bits287 plan355

def plan1008 : Plan := .step choices85 bits243 plan356

def plan1009 : Plan := .step choices85 bits244 plan357

def plan1010 : Plan := .step choices85 bits244 plan358

def plan1011 : Plan := .step choices85 bits243 plan359

def plan1012 : Plan := .step choices85 bits244 plan360

def plan1013 : Plan := .step choices85 bits290 plan361

def plan1014 : Plan := .step choices85 bits247 plan362

def plan1015 : Plan := .step choices85 bits247 plan363

def plan1016 : Plan := .step choices85 bits247 plan364

def plan1017 : Plan := .step choices85 bits242 plan365

def plan1018 : Plan := .step choices85 bits246 plan369

def plan1019 : Plan := .step choices85 bits242 plan379

def plan1020 : Plan := .step choices85 bits246 plan383

def plan1021 : Plan := .step choices86 bits293 plan361

def plan1022 : Plan := .step choices86 bits252 plan362

def plan1023 : Plan := .step choices86 bits252 plan363

def plan1024 : Plan := .step choices86 bits252 plan364

def plan1025 : Plan := .step choices86 bits251 plan369

def plan1026 : Plan := .step choices86 bits251 plan383

def plan1027 : Plan := .step choices89 bits286 plan354

def plan1028 : Plan := .step choices89 bits287 plan355

def plan1029 : Plan := .step choices89 bits243 plan356

def plan1030 : Plan := .step choices89 bits244 plan357

def plan1031 : Plan := .step choices89 bits244 plan358

def plan1032 : Plan := .step choices89 bits243 plan359

def plan1033 : Plan := .step choices89 bits244 plan360

def plan1034 : Plan := .step choices89 bits290 plan361

def plan1035 : Plan := .step choices89 bits247 plan362

def plan1036 : Plan := .step choices89 bits247 plan363

def plan1037 : Plan := .step choices89 bits247 plan364

def plan1038 : Plan := .step choices89 bits246 plan369

def plan1039 : Plan := .step choices89 bits242 plan379

def plan1040 : Plan := .step choices89 bits246 plan383

def plan1041 : Plan := .step choices90 bits293 plan361

def plan1042 : Plan := .step choices90 bits252 plan362

def plan1043 : Plan := .step choices90 bits252 plan363

def plan1044 : Plan := .step choices90 bits252 plan364

def plan1045 : Plan := .step choices90 bits251 plan383

def plan1046 : Plan := .step choices94 bits397 plan403

def plan1047 : Plan := .step choices94 bits398 plan404

def plan1048 : Plan := .step choices94 bits398 plan405

def plan1049 : Plan := .step choices94 bits397 plan406

def plan1050 : Plan := .step choices94 bits398 plan407

def plan1051 : Plan := .step choices94 bits399 plan408

def plan1052 : Plan := .step choices94 bits399 plan409

def plan1053 : Plan := .step choices94 bits399 plan410

def plan1054 : Plan := .step choices94 bits399 plan411

def plan1055 : Plan := .step choices94 bits398 plan417

def plan1056 : Plan := .step choices94 bits398 plan418

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


