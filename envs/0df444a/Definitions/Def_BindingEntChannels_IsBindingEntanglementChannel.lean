-- Prove2me | Definitions.Def_BindingEntChannels_IsBindingEntanglementChannel
-- name    : BindingEntChannels_IsBindingEntanglementChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:01.769624+00:00
-- url     : https://prove2.me/theorems/2e3e80c6-decd-4b27-82f6-13da8a05547b
-- title:
--   Binding entanglement channel: $Q_2(\Lambda)=0$ and some BE state is obtainable
-- statement:
--   A channel $\Lambda$ is a **binding entanglement channel** if
--
--   1. $Q_2(\Lambda)=0$: no quantum information can be transmitted through $\Lambda$ at a positive rate, even with two-way classical communication, and
--   2. some bipartite bound entangled state is obtainable from $\Lambda$ by (possibly multiple) uses of the channel and LQCC operations.
--
--   This is the Definition of the paper; the Theorem characterizes these channels.
--
--   **Formalization Note** Clause 1 is the operational capacity, not a property of a state; clause 2 ranges over every protocol and every output dimension. That $\Lambda$ is a channel is a hypothesis of the statements, not part of the predicate.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, Definition, pp. 1–2

import Mathlib
import Definitions.Def_BindingEntChannels_q2
import Definitions.Def_BindingEntChannels_IsObtainable
import Definitions.Def_BindingEntChannels_IsBoundEntangled

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
Definition, pp. 1–2: "We say that a channel Λ is binding entanglement channel iff (i) Q₂(Λ) = 0
and (ii) it is possible to obtain bipartite bound entangled state by means of (possibly multiply)
use of the channel and LQCC operations."

**Formalization Note.** Clause (i) is the operational two-way assisted capacity `q2 Λ = 0`
(published `RetroCorr.Separation.twoWayQuantumCapacity`); clause (ii) quantifies over every
adaptive LQCC protocol with post-selection (`IsObtainable`), every pair of output dimensions
`c, d`, and asks for a bound entangled output (`IsBoundEntangled`). Whether `Λ` is a channel is a
hypothesis of the statements, not part of this predicate. -/
def IsBindingEntanglementChannel {I O : Type*} [Fintype I] [Fintype O]
    (Λ : QAlgorithms.Superop I O) : Prop :=
  q2 Λ = 0 ∧ ∃ (c d : ℕ) (ρ : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ),
    IsObtainable Λ ρ ∧ IsBoundEntangled ρ

end BindingEntChannels


