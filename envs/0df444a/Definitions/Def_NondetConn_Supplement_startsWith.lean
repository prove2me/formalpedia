-- Prove2me | Definitions.Def_NondetConn_Supplement_startsWith
-- name    : NondetConn_Supplement_startsWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:04:55.362173+00:00
-- url     : https://prove2.me/theorems/9329c1ac-279d-4e2f-9045-259e0a414d16
-- title:
--   First sender of a public-coin protocol
-- statement:
--   A protocol **starts with Alice** (respectively, **starts with Bob**) when every public-coin communication tree with a nonempty transcript has Alice (respectively, Bob) send the first bit.
--
--   This records the paper's default Alice-first convention and the explicit Bob-first convention of Theorem B.1.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §3, p.8 (PDF p.10), and Theorem B.1, p.45 (PDF p.47)

import Definitions.Def_CommThresholdPR_StrongConverse_Protocols

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- Every public-coin tree starts with the specified party (`true` for Alice, `false` for
Bob). A zero-communication tree is allowed for either convention. -/
def startsWith {X Y A B : Type} (P : Protocol X Y A B) (alice : Bool) : Prop :=
  ∀ ω, P.publicLaw ω ≠ 0 → match P.tree ω with
    | .leaf _ _ => True
    | .alice _ _ _ => alice = true
    | .bob _ _ _ => alice = false

end NondetConn.Supplement


