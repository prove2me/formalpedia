-- Prove2me | Definitions.Def_MemQueryFeas_IsGame1Play
-- name    : MemQueryFeas_IsGame1Play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:39:21.978765+00:00
-- url     : https://prove2.me/theorems/38f2bf2b-e951-40d8-9258-6fe61b6e28d6
-- title:
--   A play of Game 1 with a compression strategy
-- statement:
--   A **compression strategy** for Game 1 consists of an encoder, which observes $E^{(\le i)}$ and its own private randomness and outputs a message, and a decoder, which based on the message, $E^{(\le i-1)}$ and its own private randomness returns vectors $x_1,\dots,x_k$. The predicate says that on a probability space nature's move holds, the encoder's and decoder's private randomness are independent of each other and of nature, and encoder and decoder are measurable.
--
--   **Formalization Note** The decoder shares no randomness with the encoder. The message space is standard Borel.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Game 1, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MemQueryFeas_IsGame1Nature

open MeasureTheory ProbabilityTheory

namespace MemQueryFeas

/-- **A play of Game 1 with a given compression strategy.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Game 1, p.12 (PDF p.13): "Encoder:
Observe `E^(≤i)` and store a message Message about these. Decoder: Based on Message and `E^(≤i−1)`
only, return nonzero vectors `x_1, …, x_k`."

`IsGame1Play μ ν d̃ T δ N E ch Uenc Udec enc dec`: Nature's move holds (`IsGame1Nature`); the
encoder's private randomness `Uenc` and the decoder's private randomness `Udec` are measurable,
independent of each other and of nature's variables `(E, ch)`; the encoder
`enc : (versions) × A → Mes` and decoder `dec : Mes × (versions) × B → (Fin k → ℝ^d)` are measurable.
The message is `enc (E^(≤i), Uenc)` and the output `dec (Message, E^(≤i−1), Udec)`
(`game1Message`, `game1Output`).

**Formalization Note.** The decoder shares no randomness with the encoder: it sees only the message,
`E^(≤i−1)` and its own private randomness ("only", line 3). The message space `Mes` is standard Borel
(required by the information quantity). Sequences of versions are passed as `ℕ → Op d` truncated by
`truncSeq`. -/
def IsGame1Play {Ω A B Mes : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace Mes] {d k : ℕ} (μ : Measure Ω) (ν : Measure (Op d)) (dt : ℕ) (T : Op d)
    (δ : ℕ → ℝ) (N : ℕ) (E : Ω → Op d) (ch : ℕ → Ω → Op d) (Uenc : Ω → A) (Udec : Ω → B)
    (enc : (ℕ → Op d) × A → Mes) (dec : Mes × (ℕ → Op d) × B → (Fin k → Vec d)) : Prop :=
  IsGame1Nature μ ν dt T δ N E ch ∧ Measurable Uenc ∧ Measurable Udec ∧
    Measurable enc ∧ Measurable dec ∧
    IndepFun (fun ω => (E ω, fun j => ch j ω)) (fun ω => (Uenc ω, Udec ω)) μ ∧
    IndepFun Uenc Udec μ

end MemQueryFeas


