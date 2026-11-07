-- Prove2me | Definitions.Def_LaconicBarrier_IPVerifier
-- name    : LaconicBarrier_IPVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:10.82262+00:00
-- url     : https://prove2.me/theorems/3548643e-1d95-44f6-a949-d431af5631c6
-- title:
--   Interactive-proof verifiers and acceptance probability
-- statement:
--   An interactive proof is a protocol between a computationally unbounded prover and a randomized verifier on a common input. The parties exchange messages, starting with the verifier, after which the verifier outputs a bit; one round is a verifier message followed by a prover reply.
--
--   A **verifier** on inputs $i$ uses $\mathrm{coins}(i)$ coins $\rho$; from the prover's messages so far it computes its next message, and after the last round its decision. A prover strategy maps the verifier's messages so far to a reply. $\Pr[\langle \mathcal P, \mathcal V\rangle(i) = 1]$ after $k$ rounds is the probability over the verifier's coins that it accepts, where a transcript whose prover messages exceed $\ell_P$ bits in total is rejected.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.2.1, p.25

import Mathlib
import Definitions.Def_LaconicBarrier_coinAvg

namespace LaconicBarrier

/-- A **verifier of an interactive proof** on common inputs of type `I` (Jain, Mathialagan, Roy,
*From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission
(manuscript sha256 1af78662…), §4.2.1, p.25: "a randomized verifier `V` … The parties exchange
messages, starting with the verifier, after which the verifier outputs a bit"; "One round consists of
a verifier message followed by a prover reply"): on input `i` it uses `coins i` coins `ρ`; given the
prover's messages so far it sends `msg i ρ`, and after the last round it outputs `dec i ρ`. -/
structure IPVerifier (I : Type) where
  /-- the number of verifier coins on input `i` -/
  coins : I → ℕ
  /-- the next verifier message, from the prover's messages so far -/
  msg : (i : I) → (Fin (coins i) → Bool) → List (List Bool) → List Bool
  /-- the decision, from all prover messages -/
  dec : (i : I) → (Fin (coins i) → Bool) → List (List Bool) → Bool

/-- The first `j` rounds against the prover strategy `P` (verifier messages so far ↦ reply): the
verifier's messages and the prover's messages. -/
def IPVerifier.transcript {I : Type} (V : IPVerifier I) (i : I) (ρ : Fin (V.coins i) → Bool)
    (P : List (List Bool) → List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | j + 1 =>
    let t := V.transcript i ρ P j
    let vs := t.1 ++ [V.msg i ρ t.2]
    (vs, t.2 ++ [P vs])

/-- `Pr[⟨P, V⟩(i) = 1]` after `k` rounds, the probability over the verifier's coins, where a
transcript whose prover messages total more than `ℓ_P` bits is rejected. -/
noncomputable def IPVerifier.accProb {I : Type} (V : IPVerifier I) (i : I) (k ℓP : ℕ)
    (P : List (List Bool) → List Bool) : ℝ :=
  coinAvg (V.coins i) fun ρ =>
    if V.dec i ρ (V.transcript i ρ P k).2 = true ∧
        ((V.transcript i ρ P k).2.map List.length).sum ≤ ℓP then 1 else 0

end LaconicBarrier


