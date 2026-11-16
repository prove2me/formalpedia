-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_OpenProtocol
-- name    : ArbLindbladLearn_Supplement_OpenProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:19:01.351354+00:00
-- url     : https://prove2.me/theorems/edc03196-371b-4511-8ded-22019d20a370
-- title:
--   Adaptive Lindbladian-access protocols with a stopping rule and no query bound
-- statement:
--   An **open-ended adaptive protocol** on $n$ qubits accesses an unknown Lindbladian $\mathcal L$ through the channels $e^{t\mathcal L}$, may use an arbitrary quantum memory (ancillas, entangled inputs), and may stop after a random number of queries, with no finite worst-case bound. It consists of:
--   1. a stopping rule: at each history $h$ of classical outcomes, whether to stop;
--   2. a memory dimension for each history, and an initial state of the system and the memory;
--   3. a duration $t_h$ for each history;
--   4. a completely positive instrument for each history, with an arbitrary measurable outcome space, mapping the system and current memory to the system and the next memory;
--   5. a two-outcome measurement $\{E_h,1-E_h\}$ for each history, used to decide when the run stops.
--
--   A run at history $h$ either stops and decides with $\{E_h,1-E_h\}$, or applies $e^{t_h\mathcal L}\otimes\mathrm{id}$ followed by the instrument, whose outcome extends the history.
--
--   These are the protocols of the proof of Theorem 5.8 ("protocols with a random number of queries and no finite worst-case query bound").
--
--   **Formalization Note** Field for field the public bounded-query `Protocol`, with the stopping rule in place of the query count; the instrument type is the public `QuantumInstrument`. Physicality is `OpenAdmissible`.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Theorem 5.8, pp.46–48

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_protocols

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open MeasureTheory
open LindbladTolerant.Testing

/-- An adaptive protocol with a stopping rule and no bound on the number of queries (proof of
Theorem 5.8, pp.46–48, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…): "protocols with a random number of queries and no finite worst-case
query bound"; the algorithms of Theorems 5.7–5.8 may use "arbitrary ancillas, entangled inputs,
quantum memory").

It mirrors the public bounded-query `LindbladTolerant.Testing.Protocol` field for field, with a
stopping rule `stop` in place of the query count `queries`. At a history `h` of classical outcomes
the run holds an unnormalized state on the system and a memory of dimension `memory h` (arbitrary,
history dependent). If `stop h`, the run halts and decides with the two-outcome measurement
`{effect h, 1 − effect h}`; otherwise it applies `e^{(duration h)ℒ} ⊗ id` (one experiment of
duration `duration h`) and then the completely positive instrument `instrument h`, whose outcome `o`
extends the history to `h ++ [o]`.

**Formalization Note** The instrument type is the public `QuantumInstrument` (arbitrary measurable
outcome spaces, finite outcome-dependent output memories). Physicality and measurability are
`OpenAdmissible`. -/
structure OpenProtocol (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  stop : List Ω → Bool
  memory : List Ω → ℕ+
  initial : Op (Qubits n × Fin (memory []))
  duration : List Ω → ℝ
  instrument : (h : List Ω) → QuantumInstrument
    (Qubits n × Fin (memory h))
    (fun o => Qubits n × Fin (memory (h ++ [o])))
  effect : (h : List Ω) → Op (Qubits n × Fin (memory h))

/-- The public bounded-query protocol with the same control data and `q` queries (used only to
reuse the public admissibility conditions, which do not involve the query count). -/
def OpenProtocol.toProtocol {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (p : OpenProtocol n Ω)
    (q : ℕ) : Protocol n Ω :=
  ⟨q, p.memory, p.initial, p.duration, p.instrument, p.effect⟩

end ArbLindbladLearn.Supplement


