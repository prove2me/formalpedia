-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Protocol
-- name    : QAdvFew_PoQOracle_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:14.54249+00:00
-- url     : https://prove2.me/theorems/3e3bf6bf-cf2e-4aac-92cc-7aff14b46c73
-- title:
--   Transcripts and acceptance probability of a protocol
-- statement:
--   A **transcript** of an $R$-round protocol with classical communication and message length $\ell$ lists, for each round, the verifier's message and then the prover's answer; after the last round the verifier outputs a bit.
--
--   Each party's behaviour is described by its likelihood: $w_V(\tau,b)$ is the probability that the verifier, receiving the prover's messages of $\tau$, sends its own messages of $\tau$ and outputs $b$, and $w_P(\tau)$ is the analogous probability for the prover. Since all messages are classical and each party's randomness and measurements are private,
--   $$
--   \Pr[(V\leftrightarrows P)\to1]=\sum_\tau w_V(\tau,1)\,w_P(\tau).
--   $$
--
--   **Formalization Note** All messages have one length $\ell$, fixed by the verifier as a polynomial in the input length. Shorter messages are padded and longer ones cut, which loses nothing because a polynomial-time verifier reads polynomially many bits.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.8, p. 13 (PDF p. 15); Definition 3.26, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A message of a protocol with message length `ℓ`. -/
abbrev Msg (ℓ : ℕ) := Fin ℓ → Bool

/-- A transcript of an `R`-round protocol with classical communication (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.8, p. 13
(PDF p. 15), Definition 3.26, p. 19 (PDF p. 21)): in round `j` the verifier sends `(τ j).1`, then
the prover sends `(τ j).2`; after round `R − 1` the verifier outputs a bit.

**Formalization Note** All messages have the same length `ℓ`, fixed by the verifier as a polynomial
in the input length; a shorter message is padded with zeros and a longer one truncated, which loses
nothing because a polynomial-time verifier reads only polynomially many bits. -/
abbrev Transcript (R ℓ : ℕ) := Fin R → Msg ℓ × Msg ℓ

namespace Transcript

/-- The messages before the verifier's message of round `j`:
`[v₀, p₀, …, v_{j−1}, p_{j−1}]`. -/
def prefixV {R ℓ : ℕ} (τ : Transcript R ℓ) (j : ℕ) : List Str :=
  ((List.finRange R).filter (fun i : Fin R => i.val < j)).flatMap
    (fun i : Fin R => [List.ofFn (τ i).1, List.ofFn (τ i).2])

/-- The messages before the prover's message of round `j`: `[v₀, p₀, …, v_{j−1}, p_{j−1}, v_j]`. -/
def prefixP {R ℓ : ℕ} (τ : Transcript R ℓ) (j : Fin R) : List Str :=
  prefixV τ j ++ [List.ofFn (τ j).1]

/-- The whole transcript as a list of messages. -/
def all {R ℓ : ℕ} (τ : Transcript R ℓ) : List Str := prefixV τ R

end Transcript

/-- A string cut or zero-padded to a message of length `ℓ`. -/
def padTo (ℓ : ℕ) (s : Str) : Msg ℓ := fun i => s.getD i false

/-- The acceptance probability of an interaction, in likelihood form. `wV τ b` is the probability
that the verifier, receiving the prover's messages of `τ`, sends its own messages of `τ` and outputs
`b`; `wP τ` is the probability that the prover, receiving the verifier's messages of `τ`, sends its
own messages of `τ`. Since every message is classical and each party's randomness and measurements
are private, the probability of the transcript `τ` with output `b` is `wV τ b · wP τ`, and
`Pr[(V ⇆ P) → 1] = Σ_τ wV τ 1 · wP τ` (Definitions 3.8, 3.26: "The probabilities are over the
parties' randomness and measurements"). -/
noncomputable def acceptProb (R ℓ : ℕ) (wV : Transcript R ℓ → Bool → ℝ) (wP : Transcript R ℓ → ℝ) :
    ℝ :=
  ∑ τ : Transcript R ℓ, wV τ true * wP τ

end QAdvFew.PoQOracle


