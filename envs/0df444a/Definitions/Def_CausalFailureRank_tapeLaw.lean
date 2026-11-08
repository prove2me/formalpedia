-- Prove2me | Definitions.Def_CausalFailureRank_tapeLaw
-- name    : CausalFailureRank_tapeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:18.777648+00:00
-- url     : https://prove2.me/theorems/64271ffd-b0d7-492b-8cfa-e9d2f65226e9
-- title:
--   Joint law of the facts and review tapes
-- statement:
--   Conditional on $X_i=x$ the review tape of stage $i$ is an infinite i.i.d. sequence from $P_i^x$; $X_i$ takes the value $1$ with probability $\pi_i(1)$. The pairs consisting of a fact and its entire tape are mutually independent across stages, so the joint law of all stages is the product of the stage laws.
--
--   **Formalization Note** Alphabets carry the discrete $\sigma$-algebra. Tapes are indexed by $\mathbb N$, since quotas may be infinite. The instances show both laws are probability measures.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.4

import Mathlib
import Definitions.Def_CausalFailureRank_Instance

open MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- The law of a stage's tape given `X_i = x`: i.i.d. draws from `P_i^x`, §2, p.4. -/
noncomputable def iidLaw (I : Instance N q) (i : Fin N) (x : Bool) : Measure (ℕ → I.α i) :=
  Measure.infinitePi fun _ : ℕ => (I.P i x).toMeasure

instance (I : Instance N q) (i : Fin N) (x : Bool) : IsProbabilityMeasure (iidLaw I i x) := by
  unfold iidLaw; infer_instance

/-- The joint law of a stage's fact and entire tape: `X_i` from the prior, then the tape i.i.d.
`P_i^{X_i}`. Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027
submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.4. -/
noncomputable def stageLaw (I : Instance N q) (i : Fin N) : Measure (Bool × (ℕ → I.α i)) :=
  ENNReal.ofReal (I.prior i) • (Measure.dirac true).prod (iidLaw I i true) +
    ENNReal.ofReal (1 - I.prior i) • (Measure.dirac false).prod (iidLaw I i false)

instance (I : Instance N q) (i : Fin N) : IsProbabilityMeasure (stageLaw I i) := by
  constructor
  have h1 := (I.prior_pos i).le
  have h2 : 0 ≤ 1 - I.prior i := by linarith [I.prior_lt_one i]
  simp only [stageLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h1 h2]
  simp

/-- A joint sample: for each stage, the fact and the entire tape. -/
abbrev Sample (I : Instance N q) : Type := ∀ i : Fin N, Bool × (ℕ → I.α i)

/-- **The joint law of all facts and tapes**, §2, p.4: "The pairs consisting of a fact and its entire
review tape are mutually independent across stages": a product measure. -/
noncomputable def tapeLaw (I : Instance N q) : Measure (Sample I) :=
  Measure.pi (stageLaw I)

instance (I : Instance N q) : IsProbabilityMeasure (tapeLaw I) := by
  unfold tapeLaw; infer_instance

end CausalFailureRank


