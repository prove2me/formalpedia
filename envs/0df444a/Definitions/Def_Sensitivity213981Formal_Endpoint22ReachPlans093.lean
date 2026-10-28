-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans093
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:07:11.583641+00:00
-- url     : https://prove2.me/theorems/71cce805-4a3d-4264-8a8b-8f06f9a2d67a
-- title:
--   Endpoint22 Reach Plans093 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans093 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8996`, `ThreeBoundEndpoint22Reachable.plan8997`, `ThreeBoundEndpoint22Reachable.plan8998`, `ThreeBoundEndpoint22Reachable.plan8999`, `ThreeBoundEndpoint22Reachable.plan9000`, `ThreeBoundEndpoint22Reachable.plan9001`, `ThreeBoundEndpoint22Reachable.plan9002`, `ThreeBoundEndpoint22Reachable.plan9003`, `ThreeBoundEndpoint22Reachable.plan9004`, `ThreeBoundEndpoint22Reachable.plan9005`, `ThreeBoundEndpoint22Reachable.plan8934`, `ThreeBoundEndpoint22Reachable.plan9006`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans093.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
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
def plan8929 : Plan := .step choices287 bits1780 plan8238

def plan8930 : Plan := .step choices287 bits1779 plan8239

def plan8931 : Plan := .step choices287 bits1783 plan8240

def plan8932 : Plan := .step choices287 bits1782 plan8241

def plan8933 : Plan := .step choices287 bits1781 plan8242

def plan8934 : Plan := .step choices287 bits1780 plan8243

def plan8935 : Plan := .step choices287 bits1779 plan8244

def plan8936 : Plan := .step choices287 bits1779 plan8299

def plan8937 : Plan := .step choices287 bits1780 plan8300

def plan8938 : Plan := .step choices287 bits1779 plan8301

def plan8939 : Plan := .step choices287 bits1781 plan8302

def plan8940 : Plan := .step choices287 bits1780 plan8303

def plan8941 : Plan := .step choices287 bits1779 plan8304

def plan8942 : Plan := .step choices287 bits1779 plan8312

def plan8943 : Plan := .step choices289 bits1797 plan8325

def plan8944 : Plan := .step choices289 bits1798 plan8326

def plan8945 : Plan := .step choices289 bits1797 plan8327

def plan8946 : Plan := .step choices289 bits1797 plan8329

def plan8947 : Plan := .step choices289 bits1797 plan8332

def plan8948 : Plan := .step choices289 bits1798 plan8334

def plan8949 : Plan := .step choices289 bits1797 plan8335

def plan8950 : Plan := .step choices289 bits1799 plan8337

def plan8951 : Plan := .step choices289 bits1797 plan8339

def plan8952 : Plan := .step choices289 bits1798 plan8341

def plan8953 : Plan := .step choices289 bits1797 plan8342

def plan8954 : Plan := .step choices289 bits1797 plan8347

def plan8955 : Plan := .step choices289 bits1798 plan8350

def plan8956 : Plan := .step choices289 bits1797 plan8351

def plan8957 : Plan := .step choices289 bits1799 plan8354

def plan8958 : Plan := .step choices289 bits1798 plan8355

def plan8959 : Plan := .step choices289 bits1797 plan8356

def plan8960 : Plan := .step choices289 bits1800 plan8359

def plan8961 : Plan := .step choices289 bits1799 plan8360

def plan8962 : Plan := .step choices289 bits1798 plan8361

def plan8963 : Plan := .step choices289 bits1797 plan8362

def plan8964 : Plan := .step choices289 bits1801 plan8365

def plan8965 : Plan := .step choices289 bits1797 plan8366

def plan8966 : Plan := .step choices289 bits1798 plan8367

def plan8967 : Plan := .step choices289 bits1797 plan8368

def plan8968 : Plan := .step choices289 bits1797 plan8370

def plan8969 : Plan := .step choices289 bits1798 plan8372

def plan8970 : Plan := .step choices289 bits1797 plan8373

def plan8971 : Plan := .step choices289 bits1799 plan8375

def plan8972 : Plan := .step choices289 bits1797 plan8377

def plan8973 : Plan := .step choices289 bits1798 plan8379

def plan8974 : Plan := .step choices289 bits1797 plan8380

def plan8975 : Plan := .step choices289 bits1800 plan8382

def plan8976 : Plan := .step choices289 bits1799 plan8383

def plan8977 : Plan := .step choices289 bits1798 plan8384

def plan8978 : Plan := .step choices289 bits1797 plan8385

def plan8979 : Plan := .step choices290 bits1797 plan8328

def plan8980 : Plan := .step choices290 bits1798 plan8329

def plan8981 : Plan := .step choices290 bits1797 plan8330

def plan8982 : Plan := .step choices290 bits1797 plan8331

def plan8983 : Plan := .step choices290 bits1798 plan8332

def plan8984 : Plan := .step choices290 bits1797 plan8333

def plan8985 : Plan := .step choices290 bits1799 plan8334

def plan8986 : Plan := .step choices290 bits1798 plan8335

def plan8987 : Plan := .step choices290 bits1797 plan8336

def plan8988 : Plan := .step choices290 bits1800 plan8337

def plan8989 : Plan := .step choices290 bits1797 plan8338

def plan8990 : Plan := .step choices290 bits1798 plan8339

def plan8991 : Plan := .step choices290 bits1797 plan8340

def plan8992 : Plan := .step choices290 bits1799 plan8341

def plan8993 : Plan := .step choices290 bits1798 plan8342

def plan8994 : Plan := .step choices290 bits1797 plan8343

def plan8995 : Plan := .step choices290 bits1797 plan8345

def plan8996 : Plan := .step choices290 bits1798 plan8347

def plan8997 : Plan := .step choices290 bits1797 plan8348

def plan8998 : Plan := .step choices290 bits1799 plan8350

def plan8999 : Plan := .step choices290 bits1798 plan8351

def plan9000 : Plan := .step choices290 bits1797 plan8352

def plan9001 : Plan := .step choices290 bits1800 plan8354

def plan9002 : Plan := .step choices290 bits1799 plan8355

def plan9003 : Plan := .step choices290 bits1798 plan8356

def plan9004 : Plan := .step choices290 bits1797 plan8357

def plan9005 : Plan := .step choices290 bits1801 plan8359

def plan9006 : Plan := .step choices290 bits1800 plan8360

def plan9007 : Plan := .step choices290 bits1799 plan8361

def plan9008 : Plan := .step choices290 bits1798 plan8362

def plan9009 : Plan := .step choices290 bits1797 plan8363

def plan9010 : Plan := .step choices290 bits1802 plan8365

def plan9011 : Plan := .step choices290 bits1797 plan8369

def plan9012 : Plan := .step choices290 bits1798 plan8370

def plan9013 : Plan := .step choices290 bits1797 plan8371

def plan9014 : Plan := .step choices290 bits1799 plan8372

def plan9015 : Plan := .step choices290 bits1798 plan8373

def plan9016 : Plan := .step choices290 bits1797 plan8374

def plan9017 : Plan := .step choices290 bits1800 plan8375

def plan9018 : Plan := .step choices290 bits1797 plan8376

def plan9019 : Plan := .step choices290 bits1798 plan8377

def plan9020 : Plan := .step choices290 bits1797 plan8378

def plan9021 : Plan := .step choices290 bits1799 plan8379

def plan9022 : Plan := .step choices290 bits1798 plan8380

def plan9023 : Plan := .step choices290 bits1797 plan8381

def plan9024 : Plan := .step choices290 bits1801 plan8382

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


