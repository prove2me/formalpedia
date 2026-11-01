-- Prove2me | Definitions.Def_OpenSearchElectionTimer
-- name    : OpenSearchElectionTimer
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T01:02:08.643808+00:00
-- url     : https://prove2.me/theorems/d3b89e46-6647-4a52-a3df-854a80d69dfb
-- title:
--   OpenSearch's randomized election timers: the random delay of an attempt, the firing times of competing candidates, uncontested rounds, and the per-round bound
-- statement:
--   A model of one round of competing randomized election timers of OpenSearch's `ElectionSchedulerFactory` at revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, over the scheduler functions transcribed by the `OpenSearchPreVote` mission (`nonNegative`, `toPositiveLongAtMost`), with Mathlib. In Java, a cluster-manager-eligible candidate's scheduler fires attempt `k` after `toPositiveLongAtMost(random.nextLong(), maxDelay) + gracePeriod` milliseconds (`ElectionSchedulerFactory.java:203-204`), where `maxDelay = min(max_timeout, initial_timeout + k · back_off_time)`, `toPositiveLongAtMost(r, M) = nonNegative(r) mod M + 1`, and the grace period is 0 for the first attempt and `cluster.election.duration` for the later ones; when an attempt fires it schedules the next one and, if the node is still a candidate that may win the election, is healthy and is commissioned, starts a new pre-voting round, closing the previous one (`Coordinator.java:1578-1608`).
--
--   **`toLong x`** — for `x : Fin (2^64)`, the integer `x − 2^63`: the `2^64` possible values of `random.nextLong()` are the elements of `Fin (2^64)`, read as Java `long`s. **`randomDelay M x`** — `toPositiveLongAtMost (toLong x) M`, the random part of the delay of an attempt with bound `M` for the draw `x`. For `M = 0`, which Java rules out (`assert 0 < upperBound`), the Lean value is `nonNegative (toLong x) + 1`. For `M = 0`, which Java rules out (`assert 0 < upperBound`), the Lean value is `nonNegative (toLong x) + 1`. **`fireTime offset bound x i`** — for `n` candidates `i : Fin n`, offsets `offset : Fin n → ℤ`, bounds `bound : Fin n → ℕ` and draws `x : Fin n → Fin (2^64)`: `offset i + randomDelay (bound i) (x i)`, the time at which candidate `i` fires; `offset i` stands for the time its timer was started plus its grace period, and `bound i` for its attempt's `maxDelay`, but only informally: no Lean term links `offset` or `bound` to `maxDelay`, `SchedulerSettings` or a grace period, and the theorems quantify over them as free parameters. **`Uncontested offset bound δ x`** — the round is uncontested with margin `δ : ℕ`: some candidate `i` fires at least `δ` before every other, `fireTime offset bound x i + δ ≤ fireTime offset bound x j` for every `j ≠ i` (a decidable predicate). **`contestedBound n δ Mmin`** — the rational number `C(n, 2) · (2δ − 1) · ⌈2^63 / Mmin⌉ / 2^63`, where `2δ − 1` is computed in the natural numbers and `⌈2^63 / Mmin⌉` is written as the natural-number quotient `(2^63 + Mmin − 1) / Mmin`, which is the ceiling when `Mmin ≥ 1`. The value is 0 when `n ≤ 1`, `δ = 0` or `Mmin = 0`, and it is not capped at 1.
--
--   Probabilities are counts: a draw of the `n` candidates of a round is a function `Fin n → Fin (2^64)`, and the probability of a set of draws is its number of elements divided by `(2^64)^n`, which is the uniform distribution with independent candidates; over `K` rounds a draw is a function `Fin K → Fin n → Fin (2^64)` and the denominator is `(2^64)^(n K)`.
--
--   **Formalization Note.** The draws are idealized. Each node's scheduler draws from the node's own `java.util.Random`, created as `new Random(Randomness.get().nextLong())` (`DiscoveryModule.java:213`) and also used by the `Coordinator` to pick a node to abdicate to (`Coordinator.java:1818`); the model treats every draw as uniform over the `2^64` longs and independent of every other draw, across nodes and attempts. `java.util.Random` is a 48-bit linear congruential generator, so `nextLong()` takes at most `2^48` of the `2^64` values, and the successive draws of one node are successive outputs of one generator; neither this nor any correlation between the seeds of different nodes is modelled. Grouping competing timers into rounds is an abstraction of the scheduler's timeline. Within a round the offsets and bounds are arbitrary integers and naturals (the theorems require every bound to lie in `[Mmin, 2^63]`); across rounds they may be any deterministic function of the earlier rounds' draws, never of the current round's. Every round has the same `n` candidates, each drawing afresh (a candidate that sits a round out can only be represented by a very large offset); the rounds need not be ordered in time, and nothing ties a round to the scheduler's attempt number. What happens between rounds is not modelled, nor whether an uncontested round leads to a successful election. Imports Mathlib and the `OpenSearchPreVote` definitions.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Mathlib
import Definitions.Def_OpenSearchPreVote

/-!
# OpenSearch cluster coordination: randomized election timers

A cluster-manager-eligible node that has no leader schedules a pre-voting round after a random delay
(`ElectionSchedulerFactory`, OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java`, cited `ESF:<line>`):
attempt `k` fires `toPositiveLongAtMost(random.nextLong(), maxDelay k) + gracePeriod` milliseconds after it was
scheduled (ESF:201-204; the timer is scheduled at ESF:240), with `maxDelay` and `toPositiveLongAtMost` transcribed in
`Def_OpenSearchPreVote`. When two candidates run at nearly the same time they can split the votes and both fail. The
randomization aims to make one candidate's timer fire far enough ahead of every other's that it runs alone, its
pre-voting round and election completing before anyone else starts. That step is informal and not modelled here:
whether a firing starts a pre-voting round at all (only if the node is still a candidate that may win the election, is
healthy and is commissioned, `Coordinator.java:1579-1608`), and whether the round and the election complete within that
head start, depend on timing and state this file does not have. The progress mission (`OpenSearchProgress`) proves that
an election succeeds in a stable period, in its sense; that an uncontested round yields such a period is not proved.

This file models one round of competing timers. Candidate `i` fires at `offset i + randomDelay (bound i) (x i)`, where
`x i` is its draw of `random.nextLong()`; `bound i` stands for its attempt's `maxDelay` and `offset i` for when its
timer was started plus the grace period, a reading that no definition here formalizes: offsets and bounds are free
parameters. The probability theorems hold whatever the offsets and bounds, even chosen by an adversary that schedules
the network (as a function of the earlier rounds' draws), provided `n ≥ 1`, `δ ≥ 1`, `Mmin ≥ 1` and every bound lies in
`[Mmin, 2^63]` (`close_pair_prob` constrains only the second timer's bound). With `Mmin = cluster.election.max_timeout`
they apply once every competing attempt has reached that timeout, which with the default settings is from attempt 99
on, counting from 0. Probabilities are counts of draws divided by `2^(64 n)`.

Idealization: each node's scheduler draws from the node's `java.util.Random` (the Coordinator's, which also uses it to
pick a node to abdicate to, `Coordinator.java:1818`), seeded from `Randomness.get().nextLong()`
(`DiscoveryModule.java:213`); the draws are modelled as uniform over the `2^64` Java `long`s and independent across
nodes and attempts. `java.util.Random` is a 48-bit linear congruential generator, so `nextLong()` takes at most `2^48`
distinct values; the model does not capture that, nor any correlation between seeds. Grouping competing timers into
rounds is itself an abstraction of the scheduler's timeline.
-/

namespace OpenSearchElectionTimer

open OpenSearchPreVote

/-- A value of `random.nextLong()`: an element of `Fin (2^64)`, read as the Java `long` `x - 2^63`. -/
def toLong (x : Fin (2 ^ 64)) : Int := (x.val : Int) - 2 ^ 63

/-- The random part of the delay of an attempt with bound `M` for the draw `x`: `toPositiveLongAtMost(x, M)`
(ESF:204). -/
def randomDelay (M : Nat) (x : Fin (2 ^ 64)) : Nat := toPositiveLongAtMost (toLong x) M

/-- The time at which candidate `i` fires, given every candidate's offset, bound and draw. -/
def fireTime {n : Nat} (offset : Fin n → Int) (bound : Fin n → Nat) (x : Fin n → Fin (2 ^ 64)) (i : Fin n) : Int :=
  offset i + randomDelay (bound i) (x i)

/-- A round is *uncontested with margin `δ`*: some candidate fires at least `δ` before every other candidate. -/
def Uncontested {n : Nat} (offset : Fin n → Int) (bound : Fin n → Nat) (δ : Nat) (x : Fin n → Fin (2 ^ 64)) : Prop :=
  ∃ i, ∀ j, j ≠ i → fireTime offset bound x i + δ ≤ fireTime offset bound x j

instance {n : Nat} (offset : Fin n → Int) (bound : Fin n → Nat) (δ : Nat) :
    DecidablePred (Uncontested offset bound δ) := fun x => by
  unfold Uncontested; infer_instance

/-- The per-round bound on the probability of a contested round: `C(n,2) · (2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63` for `δ ≥ 1`
and `Mmin ≥ 1`. It is computed with natural-number subtraction and division, so it is 0 when `δ = 0` or `Mmin = 0`, and
it is not capped at 1. -/
def contestedBound (n δ Mmin : Nat) : ℚ :=
  (n.choose 2 : ℚ) * (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63

end OpenSearchElectionTimer


