-- Prove2me | Definitions.Def_TemporalAgg_Supplement_ProactiveDue
-- name    : TemporalAgg_Supplement_ProactiveDue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:21.447964+00:00
-- url     : https://prove2.me/theorems/892430fa-bff1-4f0b-8f29-6d371c2d02d6
-- title:
--   Proactive resampling schedule $t=s+2^i$
-- statement:
--   **Proactive resampling** (Bernstein et al.) is the rule: if an object is sampled by the adversary at time $s$, the algorithm also resamples it at times $s+2^i$ for all $i\ge0$.
--
--   For a finite set $\mathrm{adv}\subseteq\mathbb N$ of adversarial sample times of an object, the object is **due** at time $t$ if
--
--   $$
--   \exists\, s\in\mathrm{adv},\ s<t,\ \exists\, i\ge 0:\ t=s+2^i .
--   $$
--
--   This is the schedule under which the walks of Theorem 1.4 and the jobs of Theorem B.1 are maintained.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.3, p.5 (box "Proactive Resampling")

import Mathlib

namespace TemporalAgg.Supplement

/-- **Proactive resampling schedule** (Bernstein et al.; Haeupler, Paramonov, *Temporal Aggregation:
Maintaining Randomness against Adaptive Adversaries*, STOC 2027 submission, manuscript of
2026-11-03, sha256 42ebf866…, §1.3, p.5): "If an object is sampled by the adversary at time `t`,
the algorithm also resamples it at times `t + 2ⁱ` for all `i ≥ 0`."

`ProactiveDue adv t` holds when the algorithm must resample at time `t` an object whose adversarial
sample times so far form the set `adv`: some `s ∈ adv` with `s < t` and `t = s + 2ⁱ`. -/
def ProactiveDue (adv : Finset ℕ) (t : ℕ) : Prop :=
  ∃ s ∈ adv, s < t ∧ ∃ i : ℕ, t = s + 2 ^ i

end TemporalAgg.Supplement


