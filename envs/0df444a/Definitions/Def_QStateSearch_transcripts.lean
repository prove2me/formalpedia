-- Prove2me | Definitions.Def_QStateSearch_transcripts
-- name    : QStateSearch_transcripts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:28.726193+00:00
-- url     : https://prove2.me/theorems/33454649-03b3-4063-abc0-c47004ea7b22
-- title:
--   Complete public transcripts of a protocol
-- statement:
--   The set of **complete public transcripts** of a step list is the finite set of all lists $(x_1,\dots,x_r)$ obtained by choosing an outcome $a\in\{0,\dots,m-1\}$ for every verifier message and a reply $z\in\{0,\dots,2^b-1\}$ for every prover message, in order. It does not depend on the prover or the oracle; the acceptance probability is a sum over it.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, pp.8–9

import Mathlib
import Definitions.Def_QStateSearch_Step

namespace QStateSearch

/-- `transcripts steps h`: the finite set of all complete public transcripts of the step list
`steps`, started after the transcript `h`: every outcome `a ∈ Fin m` of each verifier message
and every reply `z ∈ Fin (2 ^ b)` of each prover message.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, pp.8–9: "A public transcript is the round-indexed list of all transmitted
classical messages."

**Formalization Note.** Transcripts are `List ℕ` (`a.val`, `z.val` in order); the set does not
depend on the prover or the oracle. A complete run starts from `h = []`. -/
def transcripts {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] : List (Step D W) → List ℕ → Finset (List ℕ)
  | [], h => {h}
  | .unitary _ :: rest, h => transcripts rest h
  | .query :: rest, h => transcripts rest h
  | .vmsg m _ :: rest, h => Finset.univ.biUnion fun a : Fin m => transcripts rest (h ++ [a.val])
  | .pmsg b _ :: rest, h =>
      Finset.univ.biUnion fun z : Fin (2 ^ b) => transcripts rest (h ++ [z.val])

end QStateSearch


