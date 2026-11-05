-- Prove2me | Definitions.Def_BindingEntChannels_q2
-- name    : BindingEntChannels_q2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:41.037814+00:00
-- url     : https://prove2.me/theorems/491701da-3c62-44d7-b6aa-96b5427bf60c
-- title:
--   Two-way assisted quantum capacity $Q_2(\Lambda)$
-- statement:
--   For a channel $\Lambda$, $Q_2(\Lambda)\in[0,\infty]$ is the **quantum capacity assisted by two-way classical communication**: the supremum of the rates $R\ge0$ (qubits per channel use) such that for every $\eta>0$ and all sufficiently large $n$ there is a protocol transmitting any state of $\lceil Rn\rceil$ or more qubits from Alice to Bob with fidelity at least $1-\eta$ for every pure message, using $\Lambda$ exactly $n$ times together with local operations and adaptive classical communication in both directions, with no prior entanglement.
--
--   The Definition of a binding entanglement channel requires $Q_2(\Lambda)=0$.
--
--   **Formalization Note** This is the platform's two-way capacity for channels with a classical output, applied to the channel with a trivial (one-point) classical output.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 ("Here Q2 is the quantum capacity of a channel supported by LQCC action", ref. [13])

import Mathlib
import Definitions.Def_RetroCorr_Separation_TwoWay

open MeasureTheory

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2: "Q₂ is the quantum capacity of a channel supported by LQCC action (the subscript 2
indicates two-way classical communication) [13]". `q2 Λ ∈ [0, ∞]` is the supremum of the rates
(qubits per channel use) at which Alice can send arbitrary quantum states to Bob with fidelity
tending to one, using the channel `n` times together with local operations and adaptive two-way
classical communication, with no prior entanglement.

**Formalization Note.** This is the published `RetroCorr.Separation.twoWayQuantumCapacity` for
the channel with a trivial classical output: flag type `Unit`, flag law `Measure.dirac ()`,
and the constant family `fun _ => Λ`. The integral over the flag in that definition is then
evaluation at `()`. -/
noncomputable def q2 {I O : Type*} [Fintype I] [Fintype O] (Λ : QAlgorithms.Superop I O) :
    ENNReal :=
  RetroCorr.Separation.twoWayQuantumCapacity (Measure.dirac ()) (fun _ : Unit => Λ)

end BindingEntChannels


