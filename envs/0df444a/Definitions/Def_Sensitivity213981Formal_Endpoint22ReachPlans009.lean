-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans009
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:43:59.488558+00:00
-- url     : https://prove2.me/theorems/80b80669-12f2-422b-829e-8c929e880252
-- title:
--   Endpoint22 Reach Plans009 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans009 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan936`, `ThreeBoundEndpoint22Reachable.plan937`, `ThreeBoundEndpoint22Reachable.plan938`, `ThreeBoundEndpoint22Reachable.plan939`, `ThreeBoundEndpoint22Reachable.plan870`, `ThreeBoundEndpoint22Reachable.plan940`, `ThreeBoundEndpoint22Reachable.plan941`, `ThreeBoundEndpoint22Reachable.plan942`, `ThreeBoundEndpoint22Reachable.plan943`, `ThreeBoundEndpoint22Reachable.plan944`, `ThreeBoundEndpoint22Reachable.plan945`, `ThreeBoundEndpoint22Reachable.plan946`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans009.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
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
def plan865 : Plan := .step choices61 bits312 plan319

def plan866 : Plan := .step choices61 bits312 plan330

def plan867 : Plan := .step choices61 bits312 plan331

def plan868 : Plan := .step choices62 bits312 plan319

def plan869 : Plan := .step choices63 bits311 plan311

def plan870 : Plan := .step choices63 bits311 plan312

def plan871 : Plan := .step choices63 bits311 plan313

def plan872 : Plan := .step choices63 bits311 plan314

def plan873 : Plan := .step choices63 bits311 plan315

def plan874 : Plan := .step choices63 bits311 plan316

def plan875 : Plan := .step choices63 bits311 plan317

def plan876 : Plan := .step choices63 bits311 plan318

def plan877 : Plan := .step choices63 bits311 plan319

def plan878 : Plan := .step choices63 bits310 plan320

def plan879 : Plan := .step choices63 bits310 plan321

def plan880 : Plan := .step choices63 bits310 plan322

def plan881 : Plan := .step choices63 bits309 plan323

def plan882 : Plan := .step choices63 bits310 plan324

def plan883 : Plan := .step choices63 bits310 plan325

def plan884 : Plan := .step choices63 bits311 plan326

def plan885 : Plan := .step choices63 bits311 plan327

def plan886 : Plan := .step choices63 bits311 plan328

def plan887 : Plan := .step choices63 bits311 plan329

def plan888 : Plan := .step choices63 bits311 plan330

def plan889 : Plan := .step choices63 bits311 plan331

def plan890 : Plan := .step choices64 bits312 plan316

def plan891 : Plan := .step choices64 bits312 plan317

def plan892 : Plan := .step choices64 bits312 plan318

def plan893 : Plan := .step choices64 bits312 plan319

def plan894 : Plan := .step choices64 bits312 plan326

def plan895 : Plan := .step choices64 bits312 plan327

def plan896 : Plan := .step choices64 bits312 plan328

def plan897 : Plan := .step choices64 bits312 plan329

def plan898 : Plan := .step choices64 bits312 plan330

def plan899 : Plan := .step choices64 bits312 plan331

def plan900 : Plan := .step choices65 bits312 plan319

def plan901 : Plan := .step choices65 bits312 plan330

def plan902 : Plan := .step choices65 bits312 plan331

def plan903 : Plan := .step choices67 bits130 plan332

def plan904 : Plan := .step choices67 bits130 plan333

def plan905 : Plan := .step choices67 bits131 plan334

def plan906 : Plan := .step choices67 bits133 plan335

def plan907 : Plan := .step choices68 bits131 plan333

def plan908 : Plan := .step choices68 bits133 plan334

def plan909 : Plan := .step choices68 bits134 plan335

def plan910 : Plan := .step choices69 bits135 plan335

def plan911 : Plan := .step choices71 bits173 plan336

def plan912 : Plan := .step choices71 bits173 plan337

def plan913 : Plan := .step choices71 bits173 plan338

def plan914 : Plan := .step choices71 bits177 plan341

def plan915 : Plan := .step choices71 bits179 plan342

def plan916 : Plan := .step choices71 bits179 plan343

def plan917 : Plan := .step choices71 bits177 plan344

def plan918 : Plan := .step choices71 bits179 plan345

def plan919 : Plan := .step choices71 bits180 plan347

def plan920 : Plan := .step choices71 bits180 plan348

def plan921 : Plan := .step choices71 bits180 plan349

def plan922 : Plan := .step choices71 bits176 plan350

def plan923 : Plan := .step choices71 bits178 plan351

def plan924 : Plan := .step choices71 bits176 plan352

def plan925 : Plan := .step choices71 bits178 plan353

def plan926 : Plan := .step choices72 bits214 plan339

def plan927 : Plan := .step choices72 bits215 plan340

def plan928 : Plan := .step choices72 bits183 plan341

def plan929 : Plan := .step choices72 bits187 plan342

def plan930 : Plan := .step choices72 bits187 plan343

def plan931 : Plan := .step choices72 bits183 plan344

def plan932 : Plan := .step choices72 bits187 plan345

def plan933 : Plan := .step choices72 bits216 plan346

def plan934 : Plan := .step choices72 bits189 plan347

def plan935 : Plan := .step choices72 bits189 plan348

def plan936 : Plan := .step choices72 bits189 plan349

def plan937 : Plan := .step choices72 bits186 plan351

def plan938 : Plan := .step choices72 bits186 plan353

def plan939 : Plan := .step choices73 bits217 plan346

def plan940 : Plan := .step choices73 bits191 plan347

def plan941 : Plan := .step choices73 bits191 plan348

def plan942 : Plan := .step choices73 bits191 plan349

def plan943 : Plan := .step choices74 bits181 plan339

def plan944 : Plan := .step choices74 bits182 plan340

def plan945 : Plan := .step choices74 bits185 plan346

def plan946 : Plan := .step choices75 bits188 plan346

def plan947 : Plan := .step choices78 bits181 plan339

def plan948 : Plan := .step choices78 bits182 plan340

def plan949 : Plan := .step choices78 bits185 plan346

def plan950 : Plan := .step choices79 bits188 plan346

def plan951 : Plan := .step choices82 bits241 plan366

def plan952 : Plan := .step choices82 bits241 plan367

def plan953 : Plan := .step choices82 bits241 plan368

def plan954 : Plan := .step choices82 bits243 plan370

def plan955 : Plan := .step choices82 bits244 plan371

def plan956 : Plan := .step choices82 bits244 plan372

def plan957 : Plan := .step choices82 bits243 plan373

def plan958 : Plan := .step choices82 bits244 plan374

def plan959 : Plan := .step choices82 bits245 plan375

def plan960 : Plan := .step choices82 bits245 plan376

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


