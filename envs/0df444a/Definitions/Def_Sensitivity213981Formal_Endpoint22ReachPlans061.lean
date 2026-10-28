-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans061
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T01:59:17.702581+00:00
-- url     : https://prove2.me/theorems/a8e32286-b911-4763-8870-840d914b39c7
-- title:
--   Endpoint22 Reach Plans061 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans061 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5925`, `ThreeBoundEndpoint22Reachable.plan5926`, `ThreeBoundEndpoint22Reachable.plan5927`, `ThreeBoundEndpoint22Reachable.plan5928`, `ThreeBoundEndpoint22Reachable.plan5929`, `ThreeBoundEndpoint22Reachable.plan5930`, `ThreeBoundEndpoint22Reachable.plan5931`, `ThreeBoundEndpoint22Reachable.plan5862`, `ThreeBoundEndpoint22Reachable.plan5932`, `ThreeBoundEndpoint22Reachable.plan5933`, `ThreeBoundEndpoint22Reachable.plan5934`, `ThreeBoundEndpoint22Reachable.plan5935`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans061.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
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
def plan5857 : Plan := .step choices218 bits1408 plan3484

def plan5858 : Plan := .step choices218 bits1412 plan3485

def plan5859 : Plan := .step choices218 bits1434 plan3487

def plan5860 : Plan := .step choices218 bits1435 plan3488

def plan5861 : Plan := .step choices218 bits1434 plan3489

def plan5862 : Plan := .step choices218 bits1436 plan3490

def plan5863 : Plan := .step choices218 bits1435 plan3491

def plan5864 : Plan := .step choices218 bits1434 plan3492

def plan5865 : Plan := .step choices218 bits1407 plan3493

def plan5866 : Plan := .step choices218 bits1408 plan3494

def plan5867 : Plan := .step choices218 bits1407 plan3495

def plan5868 : Plan := .step choices218 bits1409 plan3496

def plan5869 : Plan := .step choices218 bits1408 plan3497

def plan5870 : Plan := .step choices218 bits1407 plan3498

def plan5871 : Plan := .step choices218 bits1410 plan3499

def plan5872 : Plan := .step choices218 bits1434 plan3500

def plan5873 : Plan := .step choices218 bits1407 plan3501

def plan5874 : Plan := .step choices218 bits1408 plan3502

def plan5875 : Plan := .step choices218 bits1407 plan3503

def plan5876 : Plan := .step choices218 bits1409 plan3504

def plan5877 : Plan := .step choices218 bits1408 plan3505

def plan5878 : Plan := .step choices218 bits1407 plan3506

def plan5879 : Plan := .step choices218 bits1411 plan3507

def plan5880 : Plan := .step choices218 bits1410 plan3508

def plan5881 : Plan := .step choices218 bits1409 plan3509

def plan5882 : Plan := .step choices218 bits1408 plan3510

def plan5883 : Plan := .step choices219 bits1409 plan3475

def plan5884 : Plan := .step choices219 bits1410 plan3476

def plan5885 : Plan := .step choices219 bits1409 plan3477

def plan5886 : Plan := .step choices219 bits1411 plan3478

def plan5887 : Plan := .step choices219 bits1410 plan3479

def plan5888 : Plan := .step choices219 bits1409 plan3480

def plan5889 : Plan := .step choices219 bits1412 plan3481

def plan5890 : Plan := .step choices219 bits1411 plan3482

def plan5891 : Plan := .step choices219 bits1410 plan3483

def plan5892 : Plan := .step choices219 bits1409 plan3484

def plan5893 : Plan := .step choices219 bits1413 plan3485

def plan5894 : Plan := .step choices219 bits1412 plan3507

def plan5895 : Plan := .step choices219 bits1411 plan3508

def plan5896 : Plan := .step choices219 bits1410 plan3509

def plan5897 : Plan := .step choices219 bits1409 plan3510

def plan5898 : Plan := .step choices220 bits1414 plan3485

def plan5899 : Plan := .step choices221 bits1429 plan3437

def plan5900 : Plan := .step choices221 bits1430 plan3438

def plan5901 : Plan := .step choices221 bits1429 plan3439

def plan5902 : Plan := .step choices221 bits1435 plan3441

def plan5903 : Plan := .step choices221 bits1436 plan3443

def plan5904 : Plan := .step choices221 bits1435 plan3444

def plan5905 : Plan := .step choices221 bits1437 plan3446

def plan5906 : Plan := .step choices221 bits1436 plan3447

def plan5907 : Plan := .step choices221 bits1435 plan3448

def plan5908 : Plan := .step choices221 bits1435 plan3454

def plan5909 : Plan := .step choices221 bits1408 plan3464

def plan5910 : Plan := .step choices221 bits1409 plan3467

def plan5911 : Plan := .step choices221 bits1408 plan3472

def plan5912 : Plan := .step choices221 bits1408 plan3476

def plan5913 : Plan := .step choices221 bits1409 plan3478

def plan5914 : Plan := .step choices221 bits1408 plan3479

def plan5915 : Plan := .step choices221 bits1410 plan3481

def plan5916 : Plan := .step choices221 bits1409 plan3482

def plan5917 : Plan := .step choices221 bits1408 plan3483

def plan5918 : Plan := .step choices221 bits1411 plan3485

def plan5919 : Plan := .step choices221 bits1408 plan3486

def plan5920 : Plan := .step choices221 bits1435 plan3490

def plan5921 : Plan := .step choices221 bits1408 plan3496

def plan5922 : Plan := .step choices221 bits1409 plan3499

def plan5923 : Plan := .step choices221 bits1408 plan3504

def plan5924 : Plan := .step choices221 bits1410 plan3507

def plan5925 : Plan := .step choices221 bits1409 plan3508

def plan5926 : Plan := .step choices221 bits1408 plan3509

def plan5927 : Plan := .step choices222 bits1435 plan3440

def plan5928 : Plan := .step choices222 bits1436 plan3441

def plan5929 : Plan := .step choices222 bits1435 plan3442

def plan5930 : Plan := .step choices222 bits1437 plan3443

def plan5931 : Plan := .step choices222 bits1436 plan3444

def plan5932 : Plan := .step choices222 bits1435 plan3445

def plan5933 : Plan := .step choices222 bits1438 plan3446

def plan5934 : Plan := .step choices222 bits1437 plan3447

def plan5935 : Plan := .step choices222 bits1436 plan3448

def plan5936 : Plan := .step choices222 bits1435 plan3449

def plan5937 : Plan := .step choices222 bits1408 plan3475

def plan5938 : Plan := .step choices222 bits1409 plan3476

def plan5939 : Plan := .step choices222 bits1408 plan3477

def plan5940 : Plan := .step choices222 bits1410 plan3478

def plan5941 : Plan := .step choices222 bits1409 plan3479

def plan5942 : Plan := .step choices222 bits1408 plan3480

def plan5943 : Plan := .step choices222 bits1411 plan3481

def plan5944 : Plan := .step choices222 bits1410 plan3482

def plan5945 : Plan := .step choices222 bits1409 plan3483

def plan5946 : Plan := .step choices222 bits1408 plan3484

def plan5947 : Plan := .step choices222 bits1412 plan3485

def plan5948 : Plan := .step choices222 bits1434 plan3487

def plan5949 : Plan := .step choices222 bits1435 plan3488

def plan5950 : Plan := .step choices222 bits1434 plan3489

def plan5951 : Plan := .step choices222 bits1436 plan3490

def plan5952 : Plan := .step choices222 bits1435 plan3491

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


