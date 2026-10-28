-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans062
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T01:58:10.588904+00:00
-- url     : https://prove2.me/theorems/940a7e16-8236-42f4-a2be-4b8e9037a188
-- title:
--   Endpoint22 Reach Plans062 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans062 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6020`, `ThreeBoundEndpoint22Reachable.plan6021`, `ThreeBoundEndpoint22Reachable.plan6022`, `ThreeBoundEndpoint22Reachable.plan6023`, `ThreeBoundEndpoint22Reachable.plan6024`, `ThreeBoundEndpoint22Reachable.plan6025`, `ThreeBoundEndpoint22Reachable.plan6026`, `ThreeBoundEndpoint22Reachable.plan6027`, `ThreeBoundEndpoint22Reachable.plan6028`, `ThreeBoundEndpoint22Reachable.plan6029`, `ThreeBoundEndpoint22Reachable.plan5958`, `ThreeBoundEndpoint22Reachable.plan6030`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans062.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
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
def plan5953 : Plan := .step choices222 bits1434 plan3492

def plan5954 : Plan := .step choices222 bits1407 plan3493

def plan5955 : Plan := .step choices222 bits1408 plan3494

def plan5956 : Plan := .step choices222 bits1407 plan3495

def plan5957 : Plan := .step choices222 bits1409 plan3496

def plan5958 : Plan := .step choices222 bits1408 plan3497

def plan5959 : Plan := .step choices222 bits1407 plan3498

def plan5960 : Plan := .step choices222 bits1410 plan3499

def plan5961 : Plan := .step choices222 bits1434 plan3500

def plan5962 : Plan := .step choices222 bits1407 plan3501

def plan5963 : Plan := .step choices222 bits1408 plan3502

def plan5964 : Plan := .step choices222 bits1407 plan3503

def plan5965 : Plan := .step choices222 bits1409 plan3504

def plan5966 : Plan := .step choices222 bits1408 plan3505

def plan5967 : Plan := .step choices222 bits1407 plan3506

def plan5968 : Plan := .step choices222 bits1411 plan3507

def plan5969 : Plan := .step choices222 bits1410 plan3508

def plan5970 : Plan := .step choices222 bits1409 plan3509

def plan5971 : Plan := .step choices222 bits1408 plan3510

def plan5972 : Plan := .step choices223 bits1413 plan3485

def plan5973 : Plan := .step choices223 bits1412 plan3507

def plan5974 : Plan := .step choices223 bits1411 plan3508

def plan5975 : Plan := .step choices223 bits1410 plan3509

def plan5976 : Plan := .step choices223 bits1409 plan3510

def plan5977 : Plan := .step choices224 bits1574 plan3511

def plan5978 : Plan := .step choices224 bits1574 plan3518

def plan5979 : Plan := .step choices224 bits1575 plan3521

def plan5980 : Plan := .step choices224 bits1574 plan3525

def plan5981 : Plan := .step choices224 bits1574 plan3529

def plan5982 : Plan := .step choices224 bits1575 plan3531

def plan5983 : Plan := .step choices224 bits1574 plan3532

def plan5984 : Plan := .step choices224 bits1576 plan3534

def plan5985 : Plan := .step choices224 bits1575 plan3535

def plan5986 : Plan := .step choices224 bits1574 plan3536

def plan5987 : Plan := .step choices224 bits1577 plan3538

def plan5988 : Plan := .step choices224 bits1574 plan3539

def plan5989 : Plan := .step choices224 bits1574 plan3543

def plan5990 : Plan := .step choices224 bits1575 plan3546

def plan5991 : Plan := .step choices224 bits1574 plan3550

def plan5992 : Plan := .step choices224 bits1576 plan3553

def plan5993 : Plan := .step choices224 bits1575 plan3554

def plan5994 : Plan := .step choices224 bits1574 plan3555

def plan5995 : Plan := .step choices225 bits1573 plan3512

def plan5996 : Plan := .step choices225 bits1574 plan3513

def plan5997 : Plan := .step choices225 bits1573 plan3514

def plan5998 : Plan := .step choices225 bits1573 plan3515

def plan5999 : Plan := .step choices225 bits1574 plan3516

def plan6000 : Plan := .step choices225 bits1573 plan3517

def plan6001 : Plan := .step choices225 bits1575 plan3518

def plan6002 : Plan := .step choices225 bits1574 plan3519

def plan6003 : Plan := .step choices225 bits1573 plan3520

def plan6004 : Plan := .step choices225 bits1576 plan3521

def plan6005 : Plan := .step choices225 bits1573 plan3522

def plan6006 : Plan := .step choices225 bits1574 plan3523

def plan6007 : Plan := .step choices225 bits1573 plan3524

def plan6008 : Plan := .step choices225 bits1575 plan3525

def plan6009 : Plan := .step choices225 bits1574 plan3526

def plan6010 : Plan := .step choices225 bits1573 plan3527

def plan6011 : Plan := .step choices225 bits1574 plan3528

def plan6012 : Plan := .step choices225 bits1575 plan3529

def plan6013 : Plan := .step choices225 bits1574 plan3530

def plan6014 : Plan := .step choices225 bits1576 plan3531

def plan6015 : Plan := .step choices225 bits1575 plan3532

def plan6016 : Plan := .step choices225 bits1574 plan3533

def plan6017 : Plan := .step choices225 bits1577 plan3534

def plan6018 : Plan := .step choices225 bits1576 plan3535

def plan6019 : Plan := .step choices225 bits1575 plan3536

def plan6020 : Plan := .step choices225 bits1574 plan3537

def plan6021 : Plan := .step choices225 bits1578 plan3538

def plan6022 : Plan := .step choices225 bits1573 plan3540

def plan6023 : Plan := .step choices225 bits1574 plan3541

def plan6024 : Plan := .step choices225 bits1573 plan3542

def plan6025 : Plan := .step choices225 bits1575 plan3543

def plan6026 : Plan := .step choices225 bits1574 plan3544

def plan6027 : Plan := .step choices225 bits1573 plan3545

def plan6028 : Plan := .step choices225 bits1576 plan3546

def plan6029 : Plan := .step choices225 bits1573 plan3547

def plan6030 : Plan := .step choices225 bits1574 plan3548

def plan6031 : Plan := .step choices225 bits1573 plan3549

def plan6032 : Plan := .step choices225 bits1575 plan3550

def plan6033 : Plan := .step choices225 bits1574 plan3551

def plan6034 : Plan := .step choices225 bits1573 plan3552

def plan6035 : Plan := .step choices225 bits1577 plan3553

def plan6036 : Plan := .step choices225 bits1576 plan3554

def plan6037 : Plan := .step choices225 bits1575 plan3555

def plan6038 : Plan := .step choices225 bits1574 plan3556

def plan6039 : Plan := .step choices226 bits1575 plan3528

def plan6040 : Plan := .step choices226 bits1576 plan3529

def plan6041 : Plan := .step choices226 bits1575 plan3530

def plan6042 : Plan := .step choices226 bits1577 plan3531

def plan6043 : Plan := .step choices226 bits1576 plan3532

def plan6044 : Plan := .step choices226 bits1575 plan3533

def plan6045 : Plan := .step choices226 bits1578 plan3534

def plan6046 : Plan := .step choices226 bits1577 plan3535

def plan6047 : Plan := .step choices226 bits1576 plan3536

def plan6048 : Plan := .step choices226 bits1575 plan3537

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


