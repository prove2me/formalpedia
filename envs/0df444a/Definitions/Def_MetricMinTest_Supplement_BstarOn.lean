-- Prove2me | Definitions.Def_MetricMinTest_Supplement_BstarOn
-- name    : MetricMinTest_Supplement_BstarOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:27:15.850202+00:00
-- url     : https://prove2.me/theorems/7a97b602-795a-4d31-b3d9-9c6a9ac533de
-- title:
--   Optimal deterministic budget $B^\star$ on a general instance class
-- statement:
--   For an instance class $\mathcal C$ with rejection set $\mathcal N$ and acceptance set $\mathcal A$, $B^\star(\mathcal C,\mathcal N,\mathcal A;\delta)$ is the least integer $N$ for which some tester valid on $(\mathcal C,\mathcal N,\mathcal A)$ uses at most $N$ queries on every input and realization.
--
--   For the superharmonic chain class of §K.1 this is $B^\star_\Gamma$.
--
--   **Formalization Note** "Every input and realization" is every private draw and every observation table; the value is $\infty$ if no valid tester has a finite budget.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6; §K.1, p.33

import Mathlib
import Definitions.Def_MetricMinTest_Supplement_IsValidOn

namespace MetricMinTest.Supplement

/-- **Optimal deterministic budget on an instance class** (`B⋆` of Definition 2.1 for a general
class). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 2.1 p.6 and §K.1 p.33.

**Formalization Note.** The least natural `N` such that some tester valid on `(cls, neg, pos)`
uses at most `N` queries for every private draw `ξ` and every observation table `ω`; an
infimum in `ℝ≥0∞`, `⊤` if there is none. -/
noncomputable def BstarOn {ι : Type} [DecidableEq ι] (cls neg pos : Set (Instance ι)) (δ : ℝ) :
    ENNReal :=
  ⨅ (N : ℕ) (_ : ∃ T : Tester ι, IsValidOn T cls neg pos δ ∧ ∀ ξ ω, T.stopTime ξ ω ≤ N),
    (N : ENNReal)

end MetricMinTest.Supplement


