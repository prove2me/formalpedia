-- Prove2me | Definitions.Def_CausalFailureRank_V
-- name    : CausalFailureRank_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:14:48.995387+00:00
-- url     : https://prove2.me/theorems/dfbf7db4-7ab9-45b8-8763-dea3bb1cec66
-- title:
--   Lawful randomized policies and the value $V_I(\delta)$
-- statement:
--   A **policy** is a map from a private seed and the visible history to actions, where the seed is drawn from an arbitrary probability space independent of the facts and tapes. It may write non-MAP values, decline corrections, delay where legal and keep spending after failure. The **value**
--   $$V_I(\delta)=\inf\{\mathbb E[C]:\ \text{policy with } \mathbb P(\text{failure})\le\delta\}$$
--   is the object Theorem 3.1 prices.
--
--   **Formalization Note** The infimum runs over the execution model; it is never the value of a recursion. It takes values in $[0,\infty]$ and is $\infty$ when the caps admit no $\delta$-safe policy. The seed's event for each history and action is required to be measurable.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.5; Theorem 3.1, p.6

import Mathlib
import Definitions.Def_CausalFailureRank_step

open MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **A lawful randomized visible-history policy.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines
Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2,
p.5: "A policy may use all visible history and private randomness, write non-MAP values, decline
corrections, delay where legal, and continue spending after failure."

**Formalization Note.** The private seed lives on an arbitrary probability space in `Type`, and is
independent of the sample through the product measure in `failProb`, `expBill`. For each history and
action the seed's event is measurable, so the integrals are genuine. -/
structure Policy (I : Instance N q) where
  /-- The seed space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of the private seed. -/
  ν : Measure Ω
  [probν : IsProbabilityMeasure ν]
  /-- The action as a function of the seed and the visible history. -/
  act : Ω → History I → Action N q
  measurable_act : ∀ h a, MeasurableSet {s | act s h = a}

attribute [instance] Policy.mΩ Policy.probν

/-- `P(failure)` of a policy: the seed and the sample are independent. -/
noncomputable def failProb (I : Instance N q) (κ : Contract) (caps : Caps N) (p : Policy I) : ENNReal :=
  (p.ν.prod (tapeLaw I)) {x | ¬ SuccessFrom I κ caps (p.act x.1) (initState I) x.2}

/-- The expected actual observation and correction charges of a policy. -/
noncomputable def expBill (I : Instance N q) (κ : Contract) (caps : Caps N) (p : Policy I) : ENNReal :=
  ∫⁻ x, billFrom I κ caps (p.act x.1) (initState I) x.2 ∂(p.ν.prod (tapeLaw I))

/-- **The value `V_I(δ)`**: the infimum, over every lawful policy with `P(failure) ≤ δ`, of the
expected actual observation and correction charges (Theorem 3.1, p.6; §2, p.5).

**Formalization Note.** An infimum over the execution model, never the value of a recursion. Valued in
`ℝ≥0∞`, so with no δ-safe policy under the given caps it is `⊤`. `V I .current` is the larger class of
contract I, with delayed execution; `V I .currentPay` is the class with immediate execution. -/
noncomputable def V (I : Instance N q) (κ : Contract) (caps : Caps N) (δ : ℝ) : ENNReal :=
  ⨅ (p : Policy I) (_ : failProb I κ caps p ≤ ENNReal.ofReal δ), expBill I κ caps p

end CausalFailureRank


