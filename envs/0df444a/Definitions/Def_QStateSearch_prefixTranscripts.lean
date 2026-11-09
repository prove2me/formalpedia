-- Prove2me | Definitions.Def_QStateSearch_prefixTranscripts
-- name    : QStateSearch_prefixTranscripts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:31.739972+00:00
-- url     : https://prove2.me/theorems/743a8b13-062a-416c-98fb-a2ee41c56934
-- title:
--   Transcripts before a query slot
-- statement:
--   For a step list and a query slot $t$ (counted from $0$), this is the finite set of public transcripts that can have been produced immediately before that slot: every outcome of each verifier message and every reply of each prover message that comes before it. It is the range of the random transcript $T_t$ of the identity-prefix execution.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 3, p.11

import Mathlib
import Definitions.Def_QStateSearch_Step

namespace QStateSearch

/-- `prefixTranscripts steps t h`: the finite set of public transcripts the step list can have
produced immediately before its query slot with 0-based index `t` (started after transcript `h`):
every verifier outcome and every prover reply of the messages before that slot.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 3, p.11: "Let T_t be its public classical transcript immediately before query t."

**Formalization Note.** Lean slot `t` is the paper's slot `t + 1`. If the list has at most `t`
query steps, the sets are the complete transcripts. -/
def prefixTranscripts {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] : List (Step D W) → ℕ → List ℕ → Finset (List ℕ)
  | [], _, h => {h}
  | .query :: _, 0, h => {h}
  | .query :: rest, t + 1, h => prefixTranscripts rest t h
  | .unitary _ :: rest, t, h => prefixTranscripts rest t h
  | .vmsg m _ :: rest, t, h =>
      Finset.univ.biUnion fun a : Fin m => prefixTranscripts rest t (h ++ [a.val])
  | .pmsg b _ :: rest, t, h =>
      Finset.univ.biUnion fun z : Fin (2 ^ b) => prefixTranscripts rest t (h ++ [z.val])

end QStateSearch


