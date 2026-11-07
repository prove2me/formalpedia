-- Prove2me | Definitions.Def_OWFLocalDesc_WeakOWFExist
-- name    : OWFLocalDesc_WeakOWFExist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:51.000116+00:00
-- url     : https://prove2.me/theorems/f1a5b1f9-7424-45d9-977b-9959b2ae4e9d
-- title:
--   Weak one-way functions exist
-- statement:
--   **Weak one-way functions exist** if some deterministic polynomial-time function $f:\{0,1\}^*\to\{0,1\}^*$ is weakly one-way in the sense of Definition 2.7.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14

import Mathlib
import Definitions.Def_OWFLocalDesc_IsWeakOWF
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Weak one-way functions exist.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.7, p.14: some
deterministic polynomial-time function on binary strings is weakly one-way. -/
def WeakOWFExist : Prop := ∃ f : List Bool → List Bool, IsWeakOWF f

end OWFLocalDesc


