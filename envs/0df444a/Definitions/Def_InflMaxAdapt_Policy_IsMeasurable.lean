-- Prove2me | Definitions.Def_InflMaxAdapt_Policy_IsMeasurable
-- name    : InflMaxAdapt_Policy_IsMeasurable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:22.491199+00:00
-- url     : https://prove2.me/theorems/7ae87da8-ab5a-4e8a-a95c-dd12083eaee9
-- title:
--   Measurable decision rules of a policy
-- statement:
--   A policy on a measurable space $\Omega$ has **measurable decision rules** if for every step $i$, every history $(C_1, \dots, C_{i-1})$ of earlier cascades and every vertex $v$, the event $\{\omega \in \Omega : \text{the rule of step } i \text{ chooses } v\}$ is measurable.
--
--   This makes the seed sequence a random variable, so that the probabilities and expectations attached to a policy are well defined.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3), definition of an adaptive policy as a random sequence

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy

open MeasureTheory

namespace InflMaxAdapt

/-- Measurability of a policy's decision rules in the external randomness (Section 1.1, printed
p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5): an adaptive policy is a *random* sequence of vertices): for every step `i`,
every history `h` of earlier cascades and every vertex `v`, the event `{ω | rule i ω h = v}` is
measurable. -/
def Policy.IsMeasurable {V : Type} {k : ℕ} {Ω : Type} [MeasurableSpace Ω] (π : Policy V k Ω) : Prop :=
  ∀ (i : Fin k) (h : Fin i.val → Finset V) (v : V), MeasurableSet {ω | π.rule i ω h = v}

end InflMaxAdapt


