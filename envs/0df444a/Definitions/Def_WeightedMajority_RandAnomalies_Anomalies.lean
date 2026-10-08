-- Prove2me | Definitions.Def_WeightedMajority_RandAnomalies_Anomalies
-- name    : WeightedMajority_RandAnomalies_Anomalies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:24.217215+00:00
-- url     : https://prove2.me/theorems/2c64be33-df72-4155-972d-4d9b798fa536
-- title:
--   The sequence class $S_\eta$ of sequences with at most $\eta$ anomalies (Section 8)
-- statement:
--   Let $X$ be an arbitrary domain and let $F$ be a pool of $\{0,1\}$-valued functions on $X$ (possibly infinite). A **trial** is a pair $(x, y)$ of an instance $x \in X$ and a label $y \in \{0,1\}$, and a **sequence of trials** is a finite list $\mathcal S = ((x_1,y_1),\dots,(x_T,y_T))$; the same instance may occur several times, with different labels.
--
--   1. The **number of anomalies** of $\mathcal S$ with respect to a function $f$ is the number of trials inconsistent with $f$:
--   $$\mathrm{anom}_f(\mathcal S) = \#\{t \le T : f(x_t) \ne y_t\}.$$
--   2. A sequence has **at most $\eta$ anomalies** with respect to the pool $F$ when some $f \in F$ has at most $\eta$ anomalies on it. $S_\eta$ is the collection of all such sequences. For nonempty $F$, this is equivalent to $\min_{f\in F}\mathrm{anom}_f(\mathcal S) \le \eta$.
--
--   $S_\eta$ is the set over which both optima of Section 8, the deterministic $\mathrm{opt}(F,\eta)$ and the randomized $\mathrm{opt}_{\mathrm{RAND}}(F,\eta)$, take their worst case.
--
--   **Formalization Note** Sequences are `Fin T → X × Bool` for every length `T`. The anomaly count and the deterministic optimum $\mathrm{opt}(F,\eta)$ are the shared definitions `WeightedMajority.Anomalies.anomalies` and `WeightedMajority.Anomalies.opt`; `InSEta` is the same predicate as the shared `HasAtMostAnomalies`, restated in this namespace.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), pp. 249–250, Section 8 (definitions of anomalies, S_η and opt(F, η))

import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt

/-!
# Littlestone and Warmuth, *The Weighted Majority Algorithm* (1994), §8: the sequence class S_η

Littlestone, Warmuth, *The Weighted Majority Algorithm*, Inform. and Comput. 108 (1994),
pp. 249–250, §8. A trial is a pair `(x, y)` of an instance and a binary label; a sequence of
trials is `S : Fin T → X × Bool`. The number of anomalies of `S` with respect to `f`
(`WeightedMajority.Anomalies.anomalies`) is the number of trials inconsistent with `f`; `S ∈ S_η`
when some `f ∈ F` has at most `η` anomalies on `S`. The deterministic optimum `opt(F, η)` is the
shared definition `WeightedMajority.Anomalies.opt`.
-/

namespace WeightedMajority.RandAnomalies

open UnderstandingML

variable {X : Type*}

/-- `S ∈ S_η` (p. 250): the sequence `S` has at most `η` anomalies with respect to the pool `F`,
i.e. some `f ∈ F` has at most `η` anomalies on `S` (the same predicate as
`WeightedMajority.Anomalies.HasAtMostAnomalies`). -/
def InSEta (F : Set (X → Bool)) (η : ℕ) {T : ℕ} (S : Fin T → X × Bool) : Prop :=
  ∃ f ∈ F, WeightedMajority.Anomalies.anomalies f S ≤ η

end WeightedMajority.RandAnomalies


