-- Prove2me | Definitions.Def_DevContest_Policy
-- name    : DevContest_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:16.988273+00:00
-- url     : https://prove2.me/theorems/74359dbf-d4c4-4a6d-837a-e13e1b8cc8c1
-- title:
--   Disclosure policies and admissible strategies
-- statement:
--   A **disclosure policy** consists of a set of messages $M$, a probability space $(U,\nu)$ of the principal's randomization, and a signal map: at time $t$, on record $r$ and draw $u$, agent $i$ receives the message $\mathrm{sig}(t,r,u,i)$. The principal commits to it at time $0$. The only restriction is that the signal at $t$ depends on the record through the record as it stands at $t$. Signals may therefore be random, private and different across agents.
--
--   A **strategy** of agent $i$ gives her effort at each date. It is **admissible** when
--
--   1. it is jointly measurable in the date, the record and the draw;
--   2. its values lie in $[0,1]$;
--   3. it uses only what $i$ knows: if two situations have the same own first-success status at $t$ and the same signals to $i$ on $[0,t]$, the effort at $t$ is the same.
--
--   Thus an agent observes her own first success and her signals, and neither the rival's success nor the draw $u$. This is the class of competitors in the optimality theorem of the mission.
--
--   **Formalization Note** The information condition is pointwise, so no path $\sigma$-algebra is needed. Private randomization of an agent is available only through the signals; on this point see footnote 7, p.10, where intermediate efforts play that role.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, §3, pp.8, 10–11; footnote 7, p.10

import Mathlib
import Definitions.Def_DevContest_Rec

open scoped ENNReal NNReal
open MeasureTheory

namespace DevContest

/-- A disclosure policy, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author
manuscript, §3, pp.10–11, and p.8 ("without imposing any restriction on the disclosure policy").
`U` carries the principal's randomization `ν`, drawn once at time `0`, and `M` is an arbitrary set
of messages. At time `t` agent `i` receives `sig t r u i`, where `r` is the record of first
successes.

**Formalization Note.** Signals may be random, private and asymmetric; the only restriction is
`nonanticipating`: the signal at `t` depends on the record only through the record as it stands at
`t`. The signal is a function of first successes because a second success ends the contest. -/
structure Policy (U M : Type) [MeasurableSpace U] where
  /-- The law of the principal's randomization. -/
  ν : Measure U
  /-- `ν` is a probability measure. -/
  isProb : IsProbabilityMeasure ν
  /-- `sig t r u i` is the message agent `i` receives at time `t`. -/
  sig : ℝ≥0 → Rec → U → Fin 2 → M
  /-- The principal cannot disclose what has not happened. -/
  nonanticipating : ∀ t r u i, sig t r u i = sig t (trunc t r) u i

/-- A strategy of one agent: her effort `y t r u` at time `t`, on record `r` and randomization `u`.
Which of these arguments she may actually use is `IsAdmissible`. -/
abbrev Strategy (U : Type) : Type := ℝ≥0 → Rec → U → ℝ

/-- A strategy is admissible for agent `i` under the policy `D` when it is jointly measurable, has
values in `[0,1]` (§3, p.10), and uses only what `i` knows at `t`: her own first success and the
signals she has received up to `t` (§3, pp.10–11).

**Formalization Note.** The information condition `info` is pointwise, so no path σ-algebra is
needed: two situations which `i` cannot tell apart at `t` get the same effort. Effort depends on the
rival's success, and on `u`, only through the signals. -/
structure IsAdmissible {U M : Type} [MeasurableSpace U] (D : Policy U M) (i : Fin 2)
    (y : Strategy U) : Prop where
  /-- Joint measurability in `(t, r, u)`. -/
  measurable : Measurable fun q : ℝ≥0 × Rec × U => y q.1 q.2.1 q.2.2
  /-- Efforts lie in `[0,1]`. -/
  mem_Icc : ∀ t r u, y t r u ∈ Set.Icc (0 : ℝ) 1
  /-- Efforts use only `i`'s own success and her signals up to `t`. -/
  info : ∀ (t : ℝ≥0) (r r' : Rec) (u u' : U), trunc t r i = trunc t r' i →
    (∀ s ≤ t, D.sig s r u i = D.sig s r' u' i) → y t r u = y t r' u'

end DevContest


