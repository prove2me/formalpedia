-- Prove2me | Definitions.Def_NondetConn_Supplement_communicationRounds
-- name    : NondetConn_Supplement_communicationRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:04:13.781207+00:00
-- url     : https://prove2.me/theorems/0ba200e1-4d8e-4a48-abe9-61de5356100f
-- title:
--   Communication rounds as alternating message blocks
-- statement:
--   A binary communication transcript is partitioned into maximal consecutive blocks sent by the same party. Its **number of communication rounds** is the number of those blocks.
--
--   Thus a message may contain several bits and consecutive messages alternate between Alice and Bob. The theorem statements bound this count on every positive-probability execution, which is the paper's worst-case $r$-round convention.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §3 Communication complexity, p.8 (PDF p.10)

import Definitions.Def_CommThresholdPR_StrongConverse_Protocols

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- The number of alternating message blocks along a binary transcript. Consecutive bits
sent by the same party form one message/round. -/
def communicationRounds {X Y A B : Type} : BinaryTree X Y A B → List Bool → ℕ :=
  let rec go (previous : Option Bool) : BinaryTree X Y A B → List Bool → ℕ
    | .leaf _ _, _ => 0
    | .alice _ _ _, [] => 0
    | .bob _ _ _, [] => 0
    | .alice _ zero one, bit :: rest =>
        (if previous = some true then 0 else 1) +
          go (some true) (if bit then one else zero) rest
    | .bob _ zero one, bit :: rest =>
        (if previous = some false then 0 else 1) +
          go (some false) (if bit then one else zero) rest
  go none

end NondetConn.Supplement


