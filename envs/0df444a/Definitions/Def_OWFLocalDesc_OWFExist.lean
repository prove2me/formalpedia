-- Prove2me | Definitions.Def_OWFLocalDesc_OWFExist
-- name    : OWFLocalDesc_OWFExist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:00.889527+00:00
-- url     : https://prove2.me/theorems/74704099-187a-495a-ac01-e662381f2a66
-- title:
--   One-way functions exist
-- statement:
--   **One-way functions exist** if some deterministic polynomial-time function $f:\{0,1\}^*\to\{0,1\}^*$ is one-way in the sense of Definition 2.7.
--
--   This is the hypothesis whose truth the mission's goal characterizes.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14

import Mathlib
import Definitions.Def_OWFLocalDesc_IsOWF
set_option autoImplicit false

namespace OWFLocalDesc

/-- **One-way functions exist.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14: some
deterministic polynomial-time function on binary strings is one-way. -/
def OWFExist : Prop := ∃ f : List Bool → List Bool, IsOWF f

end OWFLocalDesc


