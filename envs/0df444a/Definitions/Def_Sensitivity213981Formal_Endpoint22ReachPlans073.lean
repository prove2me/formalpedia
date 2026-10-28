-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans073
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:00:57.21413+00:00
-- url     : https://prove2.me/theorems/b6285586-1919-4b13-9bad-bb99eea6aacc
-- title:
--   Endpoint22 Reach Plans073 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans073 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7076`, `ThreeBoundEndpoint22Reachable.plan7077`, `ThreeBoundEndpoint22Reachable.plan7078`, `ThreeBoundEndpoint22Reachable.plan7079`, `ThreeBoundEndpoint22Reachable.plan7080`, `ThreeBoundEndpoint22Reachable.plan7081`, `ThreeBoundEndpoint22Reachable.plan7082`, `ThreeBoundEndpoint22Reachable.plan7083`, `ThreeBoundEndpoint22Reachable.plan7084`, `ThreeBoundEndpoint22Reachable.plan7085`, `ThreeBoundEndpoint22Reachable.plan7014`, `ThreeBoundEndpoint22Reachable.plan7086`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans073.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
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
def plan7009 : Plan := .step choices206 bits1493 plan5604

def plan7010 : Plan := .step choices206 bits1513 plan5622

def plan7011 : Plan := .step choices206 bits1516 plan5623

def plan7012 : Plan := .step choices206 bits1513 plan5624

def plan7013 : Plan := .step choices206 bits1519 plan5625

def plan7014 : Plan := .step choices206 bits1516 plan5626

def plan7015 : Plan := .step choices206 bits1513 plan5627

def plan7016 : Plan := .step choices206 bits1520 plan5628

def plan7017 : Plan := .step choices206 bits1519 plan5629

def plan7018 : Plan := .step choices206 bits1516 plan5630

def plan7019 : Plan := .step choices206 bits1513 plan5631

def plan7020 : Plan := .step choices206 bits1479 plan5647

def plan7021 : Plan := .step choices206 bits1492 plan5651

def plan7022 : Plan := .step choices206 bits1496 plan5652

def plan7023 : Plan := .step choices206 bits1492 plan5653

def plan7024 : Plan := .step choices206 bits1510 plan5662

def plan7025 : Plan := .step choices206 bits1512 plan5663

def plan7026 : Plan := .step choices206 bits1510 plan5664

def plan7027 : Plan := .step choices206 bits1515 plan5665

def plan7028 : Plan := .step choices206 bits1512 plan5666

def plan7029 : Plan := .step choices206 bits1510 plan5667

def plan7030 : Plan := .step choices206 bits1509 plan5679

def plan7031 : Plan := .step choices206 bits1509 plan5690

def plan7032 : Plan := .step choices206 bits1479 plan5699

def plan7033 : Plan := .step choices206 bits1492 plan5703

def plan7034 : Plan := .step choices206 bits1496 plan5704

def plan7035 : Plan := .step choices206 bits1492 plan5705

def plan7036 : Plan := .step choices206 bits1510 plan5714

def plan7037 : Plan := .step choices206 bits1512 plan5715

def plan7038 : Plan := .step choices206 bits1510 plan5716

def plan7039 : Plan := .step choices206 bits1515 plan5717

def plan7040 : Plan := .step choices206 bits1512 plan5718

def plan7041 : Plan := .step choices206 bits1510 plan5719

def plan7042 : Plan := .step choices206 bits1509 plan5731

def plan7043 : Plan := .step choices207 bits1531 plan5622

def plan7044 : Plan := .step choices207 bits1533 plan5623

def plan7045 : Plan := .step choices207 bits1531 plan5624

def plan7046 : Plan := .step choices207 bits1535 plan5625

def plan7047 : Plan := .step choices207 bits1533 plan5626

def plan7048 : Plan := .step choices207 bits1531 plan5627

def plan7049 : Plan := .step choices207 bits1537 plan5628

def plan7050 : Plan := .step choices207 bits1535 plan5629

def plan7051 : Plan := .step choices207 bits1533 plan5630

def plan7052 : Plan := .step choices207 bits1531 plan5631

def plan7053 : Plan := .step choices207 bits1529 plan5662

def plan7054 : Plan := .step choices207 bits1530 plan5663

def plan7055 : Plan := .step choices207 bits1529 plan5664

def plan7056 : Plan := .step choices207 bits1532 plan5665

def plan7057 : Plan := .step choices207 bits1530 plan5666

def plan7058 : Plan := .step choices207 bits1529 plan5667

def plan7059 : Plan := .step choices207 bits1527 plan5678

def plan7060 : Plan := .step choices207 bits1528 plan5679

def plan7061 : Plan := .step choices207 bits1527 plan5680

def plan7062 : Plan := .step choices207 bits1527 plan5689

def plan7063 : Plan := .step choices207 bits1528 plan5690

def plan7064 : Plan := .step choices207 bits1527 plan5691

def plan7065 : Plan := .step choices207 bits1529 plan5714

def plan7066 : Plan := .step choices207 bits1530 plan5715

def plan7067 : Plan := .step choices207 bits1529 plan5716

def plan7068 : Plan := .step choices207 bits1532 plan5717

def plan7069 : Plan := .step choices207 bits1530 plan5718

def plan7070 : Plan := .step choices207 bits1529 plan5719

def plan7071 : Plan := .step choices207 bits1527 plan5730

def plan7072 : Plan := .step choices207 bits1528 plan5731

def plan7073 : Plan := .step choices207 bits1527 plan5732

def plan7074 : Plan := .step choices210 bits1480 plan5554

def plan7075 : Plan := .step choices210 bits1481 plan5555

def plan7076 : Plan := .step choices210 bits1484 plan5556

def plan7077 : Plan := .step choices210 bits1481 plan5557

def plan7078 : Plan := .step choices210 bits1487 plan5558

def plan7079 : Plan := .step choices210 bits1480 plan5559

def plan7080 : Plan := .step choices210 bits1484 plan5560

def plan7081 : Plan := .step choices210 bits1481 plan5561

def plan7082 : Plan := .step choices210 bits1494 plan5562

def plan7083 : Plan := .step choices210 bits1498 plan5563

def plan7084 : Plan := .step choices210 bits1494 plan5564

def plan7085 : Plan := .step choices210 bits1501 plan5565

def plan7086 : Plan := .step choices210 bits1498 plan5566

def plan7087 : Plan := .step choices210 bits1494 plan5567

def plan7088 : Plan := .step choices210 bits1504 plan5568

def plan7089 : Plan := .step choices210 bits1501 plan5569

def plan7090 : Plan := .step choices210 bits1498 plan5570

def plan7091 : Plan := .step choices210 bits1494 plan5571

def plan7092 : Plan := .step choices210 bits1493 plan5572

def plan7093 : Plan := .step choices210 bits1497 plan5573

def plan7094 : Plan := .step choices210 bits1493 plan5574

def plan7095 : Plan := .step choices210 bits1493 plan5602

def plan7096 : Plan := .step choices210 bits1497 plan5603

def plan7097 : Plan := .step choices210 bits1493 plan5604

def plan7098 : Plan := .step choices210 bits1513 plan5622

def plan7099 : Plan := .step choices210 bits1516 plan5623

def plan7100 : Plan := .step choices210 bits1513 plan5624

def plan7101 : Plan := .step choices210 bits1519 plan5625

def plan7102 : Plan := .step choices210 bits1516 plan5626

def plan7103 : Plan := .step choices210 bits1513 plan5627

def plan7104 : Plan := .step choices210 bits1520 plan5628

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


