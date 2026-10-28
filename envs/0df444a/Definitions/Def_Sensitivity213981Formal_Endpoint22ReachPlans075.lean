-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans075
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:02:28.150988+00:00
-- url     : https://prove2.me/theorems/e40ca410-7f63-484e-9f59-889c3a09e88c
-- title:
--   Endpoint22 Reach Plans075 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans075 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7269`, `ThreeBoundEndpoint22Reachable.plan7270`, `ThreeBoundEndpoint22Reachable.plan7271`, `ThreeBoundEndpoint22Reachable.plan7272`, `ThreeBoundEndpoint22Reachable.plan7273`, `ThreeBoundEndpoint22Reachable.plan7274`, `ThreeBoundEndpoint22Reachable.plan7275`, `ThreeBoundEndpoint22Reachable.plan7206`, `ThreeBoundEndpoint22Reachable.plan7276`, `ThreeBoundEndpoint22Reachable.plan7277`, `ThreeBoundEndpoint22Reachable.plan7278`, `ThreeBoundEndpoint22Reachable.plan7279`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans075.lean, lines 1–205.

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
def plan7201 : Plan := .step choices213 bits1593 plan5957

def plan7202 : Plan := .step choices213 bits1594 plan5960

def plan7203 : Plan := .step choices213 bits1593 plan5965

def plan7204 : Plan := .step choices213 bits1595 plan5968

def plan7205 : Plan := .step choices213 bits1594 plan5969

def plan7206 : Plan := .step choices213 bits1593 plan5970

def plan7207 : Plan := .step choices213 bits1597 plan5972

def plan7208 : Plan := .step choices213 bits1596 plan5973

def plan7209 : Plan := .step choices213 bits1595 plan5974

def plan7210 : Plan := .step choices213 bits1594 plan5975

def plan7211 : Plan := .step choices213 bits1593 plan5976

def plan7212 : Plan := .step choices214 bits1599 plan5794

def plan7213 : Plan := .step choices214 bits1599 plan5796

def plan7214 : Plan := .step choices214 bits1600 plan5797

def plan7215 : Plan := .step choices214 bits1599 plan5798

def plan7216 : Plan := .step choices214 bits1599 plan5799

def plan7217 : Plan := .step choices214 bits1600 plan5800

def plan7218 : Plan := .step choices214 bits1599 plan5801

def plan7219 : Plan := .step choices214 bits1601 plan5802

def plan7220 : Plan := .step choices214 bits1600 plan5803

def plan7221 : Plan := .step choices214 bits1599 plan5804

def plan7222 : Plan := .step choices214 bits1602 plan5805

def plan7223 : Plan := .step choices214 bits1599 plan5806

def plan7224 : Plan := .step choices214 bits1599 plan5808

def plan7225 : Plan := .step choices214 bits1600 plan5809

def plan7226 : Plan := .step choices214 bits1599 plan5810

def plan7227 : Plan := .step choices214 bits1601 plan5811

def plan7228 : Plan := .step choices214 bits1600 plan5812

def plan7229 : Plan := .step choices214 bits1599 plan5813

def plan7230 : Plan := .step choices214 bits1599 plan5832

def plan7231 : Plan := .step choices214 bits1599 plan5835

def plan7232 : Plan := .step choices214 bits1600 plan5837

def plan7233 : Plan := .step choices214 bits1599 plan5838

def plan7234 : Plan := .step choices214 bits1601 plan5840

def plan7235 : Plan := .step choices214 bits1599 plan5843

def plan7236 : Plan := .step choices214 bits1600 plan5845

def plan7237 : Plan := .step choices214 bits1599 plan5846

def plan7238 : Plan := .step choices214 bits1599 plan5848

def plan7239 : Plan := .step choices214 bits1600 plan5849

def plan7240 : Plan := .step choices214 bits1599 plan5850

def plan7241 : Plan := .step choices214 bits1601 plan5851

def plan7242 : Plan := .step choices214 bits1600 plan5852

def plan7243 : Plan := .step choices214 bits1599 plan5853

def plan7244 : Plan := .step choices214 bits1602 plan5854

def plan7245 : Plan := .step choices214 bits1601 plan5855

def plan7246 : Plan := .step choices214 bits1600 plan5856

def plan7247 : Plan := .step choices214 bits1599 plan5857

def plan7248 : Plan := .step choices214 bits1603 plan5858

def plan7249 : Plan := .step choices214 bits1599 plan5866

def plan7250 : Plan := .step choices214 bits1600 plan5868

def plan7251 : Plan := .step choices214 bits1599 plan5869

def plan7252 : Plan := .step choices214 bits1601 plan5871

def plan7253 : Plan := .step choices214 bits1599 plan5874

def plan7254 : Plan := .step choices214 bits1600 plan5876

def plan7255 : Plan := .step choices214 bits1599 plan5877

def plan7256 : Plan := .step choices214 bits1602 plan5879

def plan7257 : Plan := .step choices214 bits1601 plan5880

def plan7258 : Plan := .step choices214 bits1600 plan5881

def plan7259 : Plan := .step choices214 bits1599 plan5882

def plan7260 : Plan := .step choices214 bits1600 plan5883

def plan7261 : Plan := .step choices214 bits1601 plan5884

def plan7262 : Plan := .step choices214 bits1600 plan5885

def plan7263 : Plan := .step choices214 bits1602 plan5886

def plan7264 : Plan := .step choices214 bits1601 plan5887

def plan7265 : Plan := .step choices214 bits1600 plan5888

def plan7266 : Plan := .step choices214 bits1603 plan5889

def plan7267 : Plan := .step choices214 bits1602 plan5890

def plan7268 : Plan := .step choices214 bits1601 plan5891

def plan7269 : Plan := .step choices214 bits1600 plan5892

def plan7270 : Plan := .step choices214 bits1604 plan5893

def plan7271 : Plan := .step choices214 bits1603 plan5894

def plan7272 : Plan := .step choices214 bits1602 plan5895

def plan7273 : Plan := .step choices214 bits1601 plan5896

def plan7274 : Plan := .step choices214 bits1600 plan5897

def plan7275 : Plan := .step choices214 bits1605 plan5898

def plan7276 : Plan := .step choices214 bits1599 plan5909

def plan7277 : Plan := .step choices214 bits1600 plan5910

def plan7278 : Plan := .step choices214 bits1599 plan5911

def plan7279 : Plan := .step choices214 bits1599 plan5912

def plan7280 : Plan := .step choices214 bits1600 plan5913

def plan7281 : Plan := .step choices214 bits1599 plan5914

def plan7282 : Plan := .step choices214 bits1601 plan5915

def plan7283 : Plan := .step choices214 bits1600 plan5916

def plan7284 : Plan := .step choices214 bits1599 plan5917

def plan7285 : Plan := .step choices214 bits1602 plan5918

def plan7286 : Plan := .step choices214 bits1599 plan5919

def plan7287 : Plan := .step choices214 bits1599 plan5921

def plan7288 : Plan := .step choices214 bits1600 plan5922

def plan7289 : Plan := .step choices214 bits1599 plan5923

def plan7290 : Plan := .step choices214 bits1601 plan5924

def plan7291 : Plan := .step choices214 bits1600 plan5925

def plan7292 : Plan := .step choices214 bits1599 plan5926

def plan7293 : Plan := .step choices214 bits1599 plan5937

def plan7294 : Plan := .step choices214 bits1600 plan5938

def plan7295 : Plan := .step choices214 bits1599 plan5939

def plan7296 : Plan := .step choices214 bits1601 plan5940

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


