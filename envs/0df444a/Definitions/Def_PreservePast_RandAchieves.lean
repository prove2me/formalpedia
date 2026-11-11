-- Prove2me | Definitions.Def_PreservePast_RandAchieves
-- name    : PreservePast_RandAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:41:37.368587+00:00
-- url     : https://prove2.me/theorems/a80be4da-0306-4a3b-a99b-822e7cdc8663
-- title:
--   Randomized $B$-bit retained-state protocol achieving the protective update
-- statement:
--   A **retained-state protocol** with $B$ bits consists of a probability space $(\Omega,P)$ of coins, an encoder and a decoder:
--
--   1. the encoder reads the history $h$ and the coins $\omega$ and writes a message $\mathrm{enc}(h,\omega)\in\{0,\dots,2^B-1\}$ **before** the query is known;
--   2. the decoder reads the message, the coins and the query $(x,p)$, never the history, and outputs an update $\mathrm{dec}(M,\omega,x,p)\in\mathbb R^{m\times n}$.
--
--   The protocol **achieves** the task with parameters $(r,\epsilon,\xi,R,\beta)$ when, for **every** history $h$ and **every** promised query $(x,p)$,
--   $$
--   P\{\omega:\ \mathrm{dec}(\mathrm{enc}(h,\omega),\omega,x,p)\ \text{is successful}\}\ \ge\ 1-\beta .
--   $$
--   Public randomness and private coins of either party are components of $\omega$. Codebooks and computation are unrestricted; selecting a history-dependent codeword costs bits.
--
--   **Formalization Note** The encoder is required to be measurable in $\omega$ for each history, and the decoder measurable in $\omega$ for each message and query, so that success probabilities are probabilities of measurable events (not outer measures). Messages are `Fin (2 ^ B)`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2, p.2 (PDF p.4); §3.1, p.6 (PDF p.8), (14)

import Mathlib
import Definitions.Def_PreservePast_IsPromised
import Definitions.Def_PreservePast_IsSuccess

open MeasureTheory Matrix

namespace PreservePast

/-- **A randomized B-bit retained-state protocol that achieves the protective-update task.**
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2, p.2 (PDF p.4): "an encoder reads the history H ∼ µ and writes a B-bit state M before
the query arrives. The decoder produces a response using M, the query, and public randomness U
independent of H. A B-bit state takes at most 2^B values for each public seed … Protective updates
in Section 3 must succeed for each fixed history and promised query (with probability 1 − β over
protocol coins)"; §3.1, p.6, (14): "with probability at least 1 − β for each fixed history and
promised query".

The protocol has one coin space `(Ω, P)`. The encoder `enc h ω ∈ {0, …, 2^B − 1}` reads the
history `h` (a `K`-tuple of tasks) and the coins, never the query; the decoder
`dec M ω x p` reads the message, the coins and the query `(x, p)`, never the history.
`RandAchieves P enc dec r ε ξ R β` holds when `P` is a probability measure, the encoder is
measurable in the coins for each history, the decoder is measurable in the coins for each message
and query, and for **every** history `h` and **every** promised query `(x, p)` (13) the response
is successful (14) with probability at least `1 − β` over the coins.

**Formalization Note.** Public randomness, encoder-private and decoder-private coins are all
components of the single coin `ω` (a party ignores the components it does not see). Messages are
`Fin (2 ^ B)`, so `B = 0` allows one message. Codebooks and computation are unrestricted: no
condition beyond measurability in the coins is placed on `enc` or `dec`. -/
def RandAchieves {m n K B : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (enc : (Fin K → Task W₀) → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (r : ℕ) (ε ξ R β : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ h, Measurable (enc h)) ∧
    (∀ M x p, Measurable (fun ω => Matrix.of.symm (dec M ω x p))) ∧
    ∀ h x p, IsPromised r R h x p →
      ENNReal.ofReal (1 - β) ≤ P {ω | IsSuccess r R ξ ε h x p (dec (enc h ω) ω x p)}

end PreservePast


