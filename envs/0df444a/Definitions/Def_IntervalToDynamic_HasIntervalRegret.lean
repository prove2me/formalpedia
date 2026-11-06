-- Prove2me | Definitions.Def_IntervalToDynamic_HasIntervalRegret
-- name    : IntervalToDynamic_HasIntervalRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:01.388809+00:00
-- url     : https://prove2.me/theorems/56327550-1138-4d88-925c-5906394fe37a
-- title:
--   An algorithm guarantees interval regret $r(|I|)$
-- statement:
--   The algorithm $\mathcal A$ guarantees interval regret $r(|I|)$ on $\mathcal Y$ for the class $\mathcal C$ when, for every sequence $h_1,\dots,h_T$ in $\mathcal C$, every interval $I=[a,b]\subseteq[T]$ and every $z\in\mathcal Y$,
--   $$
--   \text{I-Reg}_I(z)\le r(|I|),\qquad |I|=b-a+1,
--   $$
--   where the regret is that of the decisions of $\mathcal A$ against $h$.
--
--   **Formalization Note** The guarantee ranges over all sequences of the class. The surrogates of Algorithm 1 depend on the decisions of $\mathcal A$, so nothing weaker could be applied to the run.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 4, p.8; Eq. (4), p.5

import Mathlib
import Definitions.Def_IntervalToDynamic_decisions
import Definitions.Def_IntervalToDynamic_intervalRegret

namespace IntervalToDynamic

/-- `A` guarantees interval regret `r(|I|)` on the domain `Y` for losses of the class `C`, on every
interval of `[T]`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 4, p.8, and Eq. (4), p.5 ("simultaneously on all intervals
`I ⊆ [T]` and for all comparators").

**Formalization Note.** The guarantee ranges over **all** sequences `h` of the class: the surrogates
of Algorithm 1 depend on the decisions of `A`, so nothing weaker can be applied to the run. An
interval is `1 ≤ a ≤ b ≤ T` and `|I| = b − a + 1`. -/
def HasIntervalRegret {E : Type*} (A : OnlineAlgorithm E) (Y : Set E) (C : (E → ℝ) → Prop)
    (T : ℕ) (r : ℕ → ℝ) : Prop :=
  ∀ h : ℕ → E → ℝ, (∀ t ∈ Finset.Icc 1 T, C (h t)) →
    ∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ T → ∀ z ∈ Y,
      intervalRegret h (decisions A h) a b z ≤ r (b - a + 1)

end IntervalToDynamic


