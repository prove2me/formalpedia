-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_PSW7
-- name    : ParallelSmallWorlds_SEU_PSW7
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:30.192738+00:00
-- url     : https://prove2.me/theorems/f29c1b60-e463-44b3-be1e-539cbca9dcb7
-- title:
--   Axiom PSW7: monotone continuity of likelihood
-- statement:
--   **Axiom PSW7** says: if $R_1\supseteq R_2\supseteq\cdots$ are events with $R_i\succeq_\Theta[0,\pi]$ for every $i$ and some fixed $\pi\in[0,1]$, and $\bigcap_i R_i$ is an event, then
--
--   $$\bigcap_{i}R_i\succeq_\Theta[0,\pi].$$
--
--   This is the continuity axiom that upgrades finite additivity of the calibrated probability to countable additivity.
--
--   **Formalization Note** The intersection is required to be an event; when $Q$ is a σ-field this holds automatically and the axiom is the printed one. The sequence is indexed by $\mathbb N$ from $0$.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW7, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld

namespace ParallelSmallWorlds.SEU

/-- **Axiom PSW7 (monotone continuity).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Axiom PSW7, p.22 (PDF p.23): "if R1 ⊇ R2 ⊇ R3 ⊇ ··· is
a decreasing sequence of events in Qw such that Ri ⪰Θw [0,π], ∀i for some fixed π ∈ [0,1],
⋂_{i=1}^∞ Ri ⪰Θw [0,π]."

**Formalization Note.** The intersection is required to be an event (`⋂ Ri ∈ Qw`). When `Qw` is
a σ-field this is automatic and the axiom is exactly the printed one; when `Qw` is only a field
the axiom speaks of the intersections that are events (a reading: the paper's `⪰Θw` is not
defined on other sets). The sequence is indexed from `0`. -/
def PSW7 {Θ C : Type*} (W : SmallWorld Θ C) : Prop :=
  ∀ R : ℕ → Set Θ, (∀ i, R i ∈ W.Q) → Antitone R → (⋂ i, R i) ∈ W.Q →
    ∀ π ∈ Set.Icc (0 : ℝ) 1, (∀ i, W.lik (Sum.inl (R i)) (Sum.inr (Set.Icc 0 π))) →
      W.lik (Sum.inl (⋂ i, R i)) (Sum.inr (Set.Icc 0 π))

end ParallelSmallWorlds.SEU


