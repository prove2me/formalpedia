-- Prove2me | Definitions.Def_NondetConn_Supplement_lastSpeaker
-- name    : NondetConn_Supplement_lastSpeaker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:04:32.138902+00:00
-- url     : https://prove2.me/theorems/1770fcfb-81ce-4fd9-b08a-2fd19a8f3ed6
-- title:
--   Last speaker of a binary communication transcript
-- statement:
--   The **last speaker** of a nonempty transcript is Alice or Bob according to which party sent its final bit. This identifies the receiver of the last message, whose output is the only one required by the paper's convention.
--
--   The empty transcript has no last speaker.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §3 Communication complexity, p.8 (PDF p.10)

import Definitions.Def_CommThresholdPR_StrongConverse_Protocols

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- The party that sent the last bit along a transcript (`true` for Alice, `false` for Bob).
It is `none` for an empty or malformed transcript. -/
def lastSpeaker {X Y A B : Type} : BinaryTree X Y A B → List Bool → Option Bool
  | .leaf _ _, _ => none
  | .alice _ _ _, [] => none
  | .bob _ _ _, [] => none
  | .alice _ zero one, bit :: rest =>
      match lastSpeaker (if bit then one else zero) rest with
      | some party => some party
      | none => some true
  | .bob _ zero one, bit :: rest =>
      match lastSpeaker (if bit then one else zero) rest with
      | some party => some party
      | none => some false

end NondetConn.Supplement


