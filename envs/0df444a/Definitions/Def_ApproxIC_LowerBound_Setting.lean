-- Prove2me | Definitions.Def_ApproxIC_LowerBound_Setting
-- name    : ApproxIC_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:51.372983+00:00
-- url     : https://prove2.me/theorems/f402ff3d-3d41-4d63-b0c8-65bacd5ed5ef
-- title:
--   §2, eq. (5), p. 14 — best reporting mapping v⋆(v) ∈ argmax_{w∈S} {v·x(w) − t(w)} of a mechanism (x, t), over the shared single-buyer ε-IC model
-- statement:
--   This file adds one notion to the single-buyer mechanism design model of Balseiro, Besbes and Castro, whose objects (the value support $S=[0,\bar v]$, the density $f$, $\bar F$, $R$, $\dot R$, mechanisms $m=(x,t)$, $\mathcal M(\varepsilon)$, $\Pi$, $\Pi^\star$ and Definition 1's local $\alpha$-power envelopes) are those of the shared definition `ApproxIC.UpperBound.Setting`.
--
--   **Best reporting mapping** (eq. (5), p. 14). For a mechanism $m=(x,t)$, a buyer with value $v\in S$ who reports $w\in S$ gets utility $v\,x(w)-t(w)$. A map $v^\star:S\to S$ is a best reporting mapping for $m$ if
--   $$v^\star(v)\in\arg\max_{w\in S}\{\,v\,x(w)-t(w)\,\}\qquad\text{for every } v\in S.$$
--
--   Under $\varepsilon$-IC truthful reporting need not be optimal, so the seller must account for the buyer's best reporting mapping; Proposition 3 constructs a mechanism for which a prescribed perturbation of the hard/soft-floor reporting function is a best reporting mapping.
--
--   **Formalization Note** The mapping is a total function $r:\mathbb R\to\mathbb R$; only its values on $S$ matter, where it is required to take values in $S$ and to attain the maximum of the utility over $S$ (an argmax, not a supremum).
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 14, §2, eq. (5)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting

/-!
# Best reporting mappings (Balseiro, Besbes, Castro, arXiv:2103.03403v2, §2, eq. (5), p. 14)

The single-buyer ε-IC model of §2 (`Model`, `Standing`, `Assumption1`, `cdfBar`, `R`, `Rdot`, `Mech`,
`Mset`, `revenue`, `optRev`, `LocalPowerEnvelope`) is the shared definition `ApproxIC.UpperBound.Setting`.
This file adds the best reporting mapping of eq. (5).
-/

namespace ApproxIC.LowerBound

open ApproxIC.UpperBound

/-- A best reporting mapping (eq. (5), p. 14): "`v⋆(v) ∈ argmax_{w∈S} {v · x(w) − t(w)}`", i.e. for
every value `v ∈ S` the report `r v` lies in `S` and maximizes the buyer's utility
`v · x(w) − t(w)` over all reports `w ∈ S`. -/
def IsBestReporting (M : Model) (m : Mech) (r : ℝ → ℝ) : Prop :=
  ∀ v ∈ Set.Icc 0 M.vbar, r v ∈ Set.Icc 0 M.vbar ∧
    ∀ w ∈ Set.Icc 0 M.vbar, v * m.x w - m.t w ≤ v * m.x (r v) - m.t (r v)

end ApproxIC.LowerBound


