-- Prove2me | Definitions.Def_Submission_ThreeSum_LightRadixRows
-- name    : Submission_ThreeSum_LightRadixRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:48.645195+00:00
-- url     : https://prove2.me/theorems/43166f4e-4641-463a-8333-18d0c508a398
-- title:
--   Light Radix Rows
-- statement:
--   Definitions and structural lemmas for Light Radix Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
def body (pAffine : ℕ) : Stmt :=
  .for 6 (v 3)
    (.call pAffine [v 1,v 2 +' v 6 *' v 4,v 4,M (v 0 +' v 6),v 5] 7)
def time (m n : ℕ) : ℕ := m*(LightReportingAffine.time n+100)+20
def word (p U V : ℕ) : ℕ := U+p*V+p+1
def Inv (μ : ℕ → ℤ) (srcBase srcPrev dst p : ℕ) (base prev : List ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [srcBase,srcPrev,dst,base.length,prev.length,p,j,r],ν⟩ ∧
    Seg ν dst (step (p : ℤ) (base.take j) prev) ∧
    SameOutside μ ν dst (base.length*prev.length)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightReportingAffine.body]
end ThreeSum.LightRadixRows


