-- Prove2me | Definitions.Def_OMSRArbitrary_Policies
-- name    : OMSRArbitrary_Policies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:46.635381+00:00
-- url     : https://prove2.me/theorems/d74098d6-04b3-4390-826b-a53d0e328766
-- title:
--   Transcripts of deterministic non-anticipative policies, $O_i$, and $\mathbb E[\mathrm{OPT}]$ in the correlated model
-- statement:
--   A deterministic non-anticipative policy maps the history of its probes and their outcomes to its next probe $(i,t)$ (with $i$ available and $t$ not yet probed) or to stopping; it has no ordering restriction.
--
--   1. Its **transcript** is the sequence of its probes and observed outcomes under given edge outcomes.
--   2. The **value** of a transcript is $\sum r_i$ over its successful probes $(i,t)$.
--   3. $\mathbb E[\mathrm{OPT}]$ for a policy in the role of OPT is the expected value of its transcript in the correlated model.
--   4. $O_i$ is the set of arrivals at which the policy probes $i$; the policy **matches** $i$ if some probe of $i$ succeeds.
--
--   **Formalization Note** Policies are the published `DetPolicy`, run through the published `legalize D false`, which stops a policy at an illegal action; it may also mark an arrival as probed without probing it (action $(t,\text{none})$). The transcript's value under independent outcomes is exactly the published `deterministicValue D false`.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §2 ((Non-Anticipative) Online and Offline Policies), pp.10–11; §3.1, p.14 (O_i)

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Benchmarks
import Definitions.Def_OMSRArbitrary_PerturbedGreedy

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Outcome Seeds seedLaw DetPolicy History legalize actionBit actionReward)
noncomputable section

namespace OMSRArbitrary

variable {n m : ℕ}

/-- **The transcript of a deterministic non-anticipative policy**, arXiv:2611.03598, §2, p.10:
the sequence of probes and outcomes of the policy `π` (no ordering restriction) under the edge
outcomes `ω`, over the `m` steps it can take.

**Formalization Note.** This is the run used by the published `deterministicValue D false`: the
published `legalize D false` stops the policy at an illegal action (a probe of an unavailable
resource, of a non-edge, or of an already probed arrival), so the policy never probes an
unavailable resource, as OPT may be assumed to (p.11). -/
def transcript (D : Instance n m) (π : DetPolicy n m) (ω : Outcome D) : History n m :=
  OfflineStochMatching.UnitPatience.runPolicy (legalize D false π) (actionBit D ω) m

/-- The **value** of a transcript: the sum of `r_i` over its successful probes `(t, i)`. -/
def historyValue (D : Instance n m) (h : History n m) : ℝ :=
  (h.map (fun z => if z.2 then actionReward D z.1 else 0)).sum

/-- **Expected reward of a deterministic policy in the correlated model** (`E[OPT]` when `π` is
OPT), thresholds `z ∼ seedLaw m`, arXiv:2611.03598, §2, p.11. -/
def optValueCorr (D : Instance n m) (π : DetPolicy n m) : ℝ :=
  ∫ z, historyValue D (transcript D π (corrOutcome D z)) ∂seedLaw m

/-- **`O_i`**: the set of arrivals at which the policy `π` probes resource `i` on thresholds `z`
(arXiv:2611.03598, §3.1, p.14: "Let O_i denote the set of arrivals at which i is probed by OPT"). -/
def optProbeSet (D : Instance n m) (π : DetPolicy n m) (z : Seeds m) (i : Fin n) :
    Finset (Fin m) :=
  ((transcript D π (corrOutcome D z)).filterMap
    (fun e => if e.1.2 = some i then some e.1.1 else none)).toFinset

/-- The policy `π` **matches `i`** on thresholds `z`: some probe of `i` succeeds. -/
def optMatches (D : Instance n m) (π : DetPolicy n m) (z : Seeds m) (i : Fin n) : Prop :=
  ∃ t : Fin m, ((t, some i), true) ∈ transcript D π (corrOutcome D z)

end OMSRArbitrary


