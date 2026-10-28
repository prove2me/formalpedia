-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans076
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:01:24.454368+00:00
-- url     : https://prove2.me/theorems/04ba94d4-bd0f-46d7-a703-3650b983f3b3
-- title:
--   Endpoint22 Reach Plans076 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans076 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7365`, `ThreeBoundEndpoint22Reachable.plan7366`, `ThreeBoundEndpoint22Reachable.plan7367`, `ThreeBoundEndpoint22Reachable.plan7368`, `ThreeBoundEndpoint22Reachable.plan7369`, `ThreeBoundEndpoint22Reachable.plan7370`, `ThreeBoundEndpoint22Reachable.plan7371`, `ThreeBoundEndpoint22Reachable.plan7302`, `ThreeBoundEndpoint22Reachable.plan7372`, `ThreeBoundEndpoint22Reachable.plan7373`, `ThreeBoundEndpoint22Reachable.plan7374`, `ThreeBoundEndpoint22Reachable.plan7375`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans076.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
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
def plan7297 : Plan := .step choices214 bits1600 plan5941

def plan7298 : Plan := .step choices214 bits1599 plan5942

def plan7299 : Plan := .step choices214 bits1602 plan5943

def plan7300 : Plan := .step choices214 bits1601 plan5944

def plan7301 : Plan := .step choices214 bits1600 plan5945

def plan7302 : Plan := .step choices214 bits1599 plan5946

def plan7303 : Plan := .step choices214 bits1603 plan5947

def plan7304 : Plan := .step choices214 bits1599 plan5955

def plan7305 : Plan := .step choices214 bits1600 plan5957

def plan7306 : Plan := .step choices214 bits1599 plan5958

def plan7307 : Plan := .step choices214 bits1601 plan5960

def plan7308 : Plan := .step choices214 bits1599 plan5963

def plan7309 : Plan := .step choices214 bits1600 plan5965

def plan7310 : Plan := .step choices214 bits1599 plan5966

def plan7311 : Plan := .step choices214 bits1602 plan5968

def plan7312 : Plan := .step choices214 bits1601 plan5969

def plan7313 : Plan := .step choices214 bits1600 plan5970

def plan7314 : Plan := .step choices214 bits1599 plan5971

def plan7315 : Plan := .step choices214 bits1604 plan5972

def plan7316 : Plan := .step choices214 bits1603 plan5973

def plan7317 : Plan := .step choices214 bits1602 plan5974

def plan7318 : Plan := .step choices214 bits1601 plan5975

def plan7319 : Plan := .step choices214 bits1600 plan5976

def plan7320 : Plan := .step choices215 bits1606 plan5831

def plan7321 : Plan := .step choices215 bits1607 plan5832

def plan7322 : Plan := .step choices215 bits1606 plan5833

def plan7323 : Plan := .step choices215 bits1606 plan5834

def plan7324 : Plan := .step choices215 bits1607 plan5835

def plan7325 : Plan := .step choices215 bits1606 plan5836

def plan7326 : Plan := .step choices215 bits1608 plan5837

def plan7327 : Plan := .step choices215 bits1607 plan5838

def plan7328 : Plan := .step choices215 bits1606 plan5839

def plan7329 : Plan := .step choices215 bits1609 plan5840

def plan7330 : Plan := .step choices215 bits1606 plan5842

def plan7331 : Plan := .step choices215 bits1607 plan5843

def plan7332 : Plan := .step choices215 bits1606 plan5844

def plan7333 : Plan := .step choices215 bits1608 plan5845

def plan7334 : Plan := .step choices215 bits1607 plan5846

def plan7335 : Plan := .step choices215 bits1606 plan5847

def plan7336 : Plan := .step choices215 bits1607 plan5848

def plan7337 : Plan := .step choices215 bits1608 plan5849

def plan7338 : Plan := .step choices215 bits1607 plan5850

def plan7339 : Plan := .step choices215 bits1609 plan5851

def plan7340 : Plan := .step choices215 bits1608 plan5852

def plan7341 : Plan := .step choices215 bits1607 plan5853

def plan7342 : Plan := .step choices215 bits1610 plan5854

def plan7343 : Plan := .step choices215 bits1609 plan5855

def plan7344 : Plan := .step choices215 bits1608 plan5856

def plan7345 : Plan := .step choices215 bits1607 plan5857

def plan7346 : Plan := .step choices215 bits1611 plan5858

def plan7347 : Plan := .step choices215 bits1606 plan5865

def plan7348 : Plan := .step choices215 bits1607 plan5866

def plan7349 : Plan := .step choices215 bits1606 plan5867

def plan7350 : Plan := .step choices215 bits1608 plan5868

def plan7351 : Plan := .step choices215 bits1607 plan5869

def plan7352 : Plan := .step choices215 bits1606 plan5870

def plan7353 : Plan := .step choices215 bits1609 plan5871

def plan7354 : Plan := .step choices215 bits1606 plan5873

def plan7355 : Plan := .step choices215 bits1607 plan5874

def plan7356 : Plan := .step choices215 bits1606 plan5875

def plan7357 : Plan := .step choices215 bits1608 plan5876

def plan7358 : Plan := .step choices215 bits1607 plan5877

def plan7359 : Plan := .step choices215 bits1606 plan5878

def plan7360 : Plan := .step choices215 bits1610 plan5879

def plan7361 : Plan := .step choices215 bits1609 plan5880

def plan7362 : Plan := .step choices215 bits1608 plan5881

def plan7363 : Plan := .step choices215 bits1607 plan5882

def plan7364 : Plan := .step choices215 bits1608 plan5883

def plan7365 : Plan := .step choices215 bits1609 plan5884

def plan7366 : Plan := .step choices215 bits1608 plan5885

def plan7367 : Plan := .step choices215 bits1610 plan5886

def plan7368 : Plan := .step choices215 bits1609 plan5887

def plan7369 : Plan := .step choices215 bits1608 plan5888

def plan7370 : Plan := .step choices215 bits1611 plan5889

def plan7371 : Plan := .step choices215 bits1610 plan5890

def plan7372 : Plan := .step choices215 bits1609 plan5891

def plan7373 : Plan := .step choices215 bits1608 plan5892

def plan7374 : Plan := .step choices215 bits1612 plan5893

def plan7375 : Plan := .step choices215 bits1611 plan5894

def plan7376 : Plan := .step choices215 bits1610 plan5895

def plan7377 : Plan := .step choices215 bits1609 plan5896

def plan7378 : Plan := .step choices215 bits1608 plan5897

def plan7379 : Plan := .step choices215 bits1613 plan5898

def plan7380 : Plan := .step choices215 bits1607 plan5937

def plan7381 : Plan := .step choices215 bits1608 plan5938

def plan7382 : Plan := .step choices215 bits1607 plan5939

def plan7383 : Plan := .step choices215 bits1609 plan5940

def plan7384 : Plan := .step choices215 bits1608 plan5941

def plan7385 : Plan := .step choices215 bits1607 plan5942

def plan7386 : Plan := .step choices215 bits1610 plan5943

def plan7387 : Plan := .step choices215 bits1609 plan5944

def plan7388 : Plan := .step choices215 bits1608 plan5945

def plan7389 : Plan := .step choices215 bits1607 plan5946

def plan7390 : Plan := .step choices215 bits1611 plan5947

def plan7391 : Plan := .step choices215 bits1606 plan5954

def plan7392 : Plan := .step choices215 bits1607 plan5955

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


