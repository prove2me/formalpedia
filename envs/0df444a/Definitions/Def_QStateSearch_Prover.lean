-- Prove2me | Definitions.Def_QStateSearch_Prover
-- name    : QStateSearch_Prover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:29.53435+00:00
-- url     : https://prove2.me/theorems/1969df4a-cb7b-42eb-b0f6-5c6768ed9879
-- title:
--   Deterministic classical prover
-- statement:
--   A **deterministic classical prover** $P$ assigns to every public transcript $h$ and every padded message length $b$ a reply $P(h,b)\in\{0,\dots,2^b-1\}$. It sees only the public transcript: not the verifier's quantum state and not its private outcomes. No efficiency or uniformity condition is imposed.
--
--   **Formalization Note** A public transcript is the list of natural numbers recording, in order, each verifier message $a$ and each prover reply $z$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.9

import Mathlib

namespace QStateSearch

/-- A deterministic classical prover: after the public transcript `h`, when a padded `b`-bit
message is due, it replies `P h b ∈ Fin (2 ^ b)`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.9: "On a fixed input, a deterministic classical prover simply specifies
one classical reply after every possible public transcript. We write this reply as P(h), where
h is the transcript. No efficiency or uniformity condition is imposed on P."

**Formalization Note.** A public transcript is a `List ℕ` recording, in order, `a.val` for each
verifier message `a ∈ Fin m` and `z.val` for each prover message `z ∈ Fin (2 ^ b)`. The prover
sees only the transcript, never the verifier's quantum state or private outcomes. -/
def Prover : Type := List ℕ → (b : ℕ) → Fin (2 ^ b)

end QStateSearch


