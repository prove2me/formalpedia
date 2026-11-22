-- Prove2me | Definitions.Def_PreservePast_Supplement_StateProtocol
-- name    : PreservePast_Supplement_StateProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:11.854385+00:00
-- url     : https://prove2.me/theorems/73b2c66b-5993-4763-a484-4678076fd710
-- title:
--   Retained-state protocols with public coins, their success, retained information, register width, and the full-data optimum
-- statement:
--   A **retained-state protocol** for data in $\mathcal D$, test queries in $Z$ and predictions in $\mathrm{Out}$ consists of independent public coins $R$, private encoder randomness, a message alphabet, a jointly measurable encoder producing the message $M$ from the data, $R$ and the private randomness, and a jointly measurable decoder producing a prediction from $(M,R,\text{query})$.
--
--   An **experiment** is a latent variable with law $\nu$, the data shown to the encoder (a function of the latent variable) and, for each latent value, the joint law of the test query and its correct answer. In it:
--
--   - the **success** of a protocol is the probability that the decoder returns the correct answer;
--   - the **retained information** $I(V;M\mid S,R)$, in bits, of a target $V$ given side information $S$ (both functions of the latent variable) is the published `PreservePast.cmiBits`;
--   - the protocol **has width $B$** if its message takes at most $2^B$ values;
--   - the **full-data optimum** $S^\ast$ is the supremum of the success of jointly measurable decoders that see the whole data and the query.
--
--   The **identification test law** for records $x_1,\dots,x_k$ and a query channel $P$ draws $J$ uniformly from $\{1,\dots,k\}$ and the query from $P_{x_J}$.
--
--   **Formalization Note** The message alphabet is standard Borel. Decoder coins are part of the public coins. The success is a lower integral converted to a real number.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §1.2, p.2 (PDF p.4); Definition 1, p.10 (PDF p.12); §H.3, p.48 (PDF p.50); §K.2, p.57 (PDF p.59)

import Mathlib
import Definitions.Def_PreservePast_cmiBits

open MeasureTheory
open scoped Classical

namespace PreservePast.Supplement

/-- **A retained-state protocol with public coins and a possibly randomized message**, for data in
`𝒟`, test queries in `Z` and predictions in `Out`. P. Xu, *Information Required to Preserve Past
Learning*, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2, p.2 (PDF p.4):
"an encoder reads the history … and writes a B-bit state M before the query arrives. The decoder
produces a response using M, the query, and public randomness"; Definition 1, p.10 (PDF p.12):
"An encoder observes X and independent public coins R and produces a possibly randomized message
M. … The decoder observes (M, R, Z) and predicts J"; §K.2, p.57 (PDF p.59): "The learner retains
M and predicts a fresh label from its feature and public coins R".

**Formalization Note.** `ΩR` carries the public coins `R`, `ΩE` the encoder's private randomness,
`Msg` is the message alphabet (standard Borel, so that conditional mutual information is
defined). Encoder and decoder are jointly measurable. Decoder coins are part of `R` ("Exposing
decoder coins as an independent seed unused by the encoder makes decision regions deterministic
without changing either cost or success", p.10). It is the protocol shape of this mission's
`IdProtocol` (Definition 1) for an arbitrary data, query and output type. -/
structure StateProtocol (𝒟 Z Out : Type) [MeasurableSpace 𝒟] [MeasurableSpace Z]
    [MeasurableSpace Out] : Type 1 where
  /-- Public coins. -/
  ΩR : Type
  /-- Private encoder randomness. -/
  ΩE : Type
  /-- Message alphabet. -/
  Msg : Type
  [mR : MeasurableSpace ΩR]
  [mE : MeasurableSpace ΩE]
  [mM : MeasurableSpace Msg]
  [sbM : StandardBorelSpace Msg]
  [neM : Nonempty Msg]
  /-- Law of the public coins. -/
  PR : Measure ΩR
  /-- Law of the private randomness. -/
  PE : Measure ΩE
  [probR : IsProbabilityMeasure PR]
  [probE : IsProbabilityMeasure PE]
  /-- The encoder. -/
  enc : 𝒟 → ΩR → ΩE → Msg
  /-- The decoder. -/
  dec : Msg → ΩR → Z → Out
  enc_meas : Measurable fun q : 𝒟 × ΩR × ΩE => enc q.1 q.2.1 q.2.2
  dec_meas : Measurable fun q : Msg × ΩR × Z => dec q.1 q.2.1 q.2.2

attribute [instance] StateProtocol.mR StateProtocol.mE StateProtocol.mM StateProtocol.sbM
  StateProtocol.neM StateProtocol.probR StateProtocol.probE

/-- The **success probability** of a protocol in an experiment given by a latent law `ν` on `Λ`,
the data `data : Λ → 𝒟` shown to the encoder, and, for each latent value, the joint law
`test l` of the test query and its correct answer: the probability, over the latent variable,
the test pair and all coins, that the decoder returns the correct answer.

**Formalization Note.** A lower integral in `ℝ≥0∞` converted to a real number (it is at most `1`
for probability laws), so no integrability question arises. -/
noncomputable def StateProtocol.success {𝒟 Z Out : Type} [MeasurableSpace 𝒟] [MeasurableSpace Z]
    [MeasurableSpace Out] (π : StateProtocol 𝒟 Z Out) {Λ : Type} [MeasurableSpace Λ]
    (ν : Measure Λ) (data : Λ → 𝒟) (test : Λ → Measure (Z × Out)) : ℝ :=
  (∫⁻ l, ∫⁻ t, (π.PR.prod π.PE) {q | π.dec (π.enc (data l) q.1 q.2) q.1 t.1 = t.2}
    ∂(test l) ∂ν).toReal

/-- The **retained information** `I(V; M | S, R)` in bits, for a target variable `V = target l`
and side information `S = side l`, both functions of the latent variable, where `M` is the
message and `R` the public coins: the published conditional mutual information `cmiBits` on the
space of the latent variable, the public coins and the private randomness, conditioning on the
pair `(S, R)`. With `side` constant this is `I(V; M | R)`. -/
noncomputable def StateProtocol.info {𝒟 Z Out : Type} [MeasurableSpace 𝒟] [MeasurableSpace Z]
    [MeasurableSpace Out] (π : StateProtocol 𝒟 Z Out) {Λ V S : Type} [MeasurableSpace Λ]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V] [MeasurableSpace S]
    (ν : Measure Λ) [IsFiniteMeasure ν] (data : Λ → 𝒟) (target : Λ → V) (side : Λ → S) : ENNReal :=
  cmiBits (ν.prod (π.PR.prod π.PE)) (fun w => target w.1)
    (fun w => π.enc (data w.1) w.2.1 w.2.2) (fun w => (side w.1, w.2.1))

/-- The message fits a **fixed register of width `B`**: it takes at most `2^B` values. -/
def StateProtocol.HasWidth {𝒟 Z Out : Type} [MeasurableSpace 𝒟] [MeasurableSpace Z]
    [MeasurableSpace Out] (π : StateProtocol 𝒟 Z Out) (B : ℕ) : Prop :=
  Finite π.Msg ∧ Nat.card π.Msg ≤ 2 ^ B

/-- The **full-data optimum** `S*` of an experiment: the largest success of a decoder that sees
the whole data and the test query (Definition 1, p.10: "S* denotes the optimal success when the
decoder also has the full X"; §K.2, p.57: "L* is the full-sample optimum"; Theorem 16, p.58:
"The full-training-data Bayes success").

**Formalization Note.** A real `⨆` of success probabilities (all in `[0, 1]`) over the jointly
measurable deterministic decoders `𝒟 → Z → Out`; randomizing the decoder cannot increase the
optimum. The index type is nonempty when `Out` is. -/
noncomputable def fullDataOptimum {𝒟 Z Out Λ : Type} [MeasurableSpace 𝒟] [MeasurableSpace Z]
    [MeasurableSpace Out] [MeasurableSpace Λ] (ν : Measure Λ) (data : Λ → 𝒟)
    (test : Λ → Measure (Z × Out)) : ℝ :=
  ⨆ dec : {dec : 𝒟 → Z → Out // Measurable fun q : 𝒟 × Z => dec q.1 q.2},
    (∫⁻ l, (test l) {t | dec.1 (data l) t.1 = t.2} ∂ν).toReal

/-- The **test law of an identification experiment** with `k` records `x : Fin k → X` and query
channel `P`: the index `J` is uniform on `Fin k` and, given `J = j`, the query has law `P (x j)`
(Definition 1, p.10; §H.3, p.48: "the queried index is uniform and independent of the records
and coins"). The joint law of `(Z, J)`. -/
noncomputable def idTest {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] {k : ℕ}
    (P : X → Measure Z) (x : Fin k → X) : Measure (Z × Fin k) :=
  ∑ j : Fin k, ((k : ENNReal))⁻¹ • (P (x j)).map (fun z => (z, j))

end PreservePast.Supplement


