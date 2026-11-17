-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_PricingRegretBound
-- name    : CalibeatBandit_Supplement_PricingRegretBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:29:53.992678+00:00
-- url     : https://prove2.me/theorems/f3e8ff55-8346-437a-8fdc-3b0dd6ac0c6a
-- title:
--   Regret bounds $\mathbb E[\mathrm{SR}_T]\le a$, $\mathbb E[\mathrm{Rec}_T]\le b$ of a dynamic pricing algorithm
-- statement:
--   A dynamic pricing algorithm satisfies **$\mathbb E[\mathrm{SR}_T]\le a$ and $\mathbb E[\mathrm{Rec}_T]\le b$ for $K$-sparse recommendations and non-increasing demands** (cost $c$, horizon $T$) if, for every set of at most $K$ recommended prices in $[0,1]$ and every run of the pricing protocol of §2.2 on every probability space,
--   $$\mathbb E^*[\mathrm{SR}_T]\le a,\qquad\mathbb E^*[\mathrm{Rec}_T]\le b .$$
--   Here $\mathbb E^*[f]\le b$ means that some integrable $g\ge f$ (almost surely) has $\mathbb E[g]\le b$.
--
--   Theorem 5.1 states these bounds, and with $a=b=\varepsilon T$ they are $(\varepsilon,\varepsilon)$-calibeating (Definition 2.2) in the pricing setting.
--
--   **Formalization Note** $\mathrm{SR}_T$ and $\mathrm{Rec}_T$ are suprema over uncountably many maps, so their measurability is not automatic. $\mathbb E^*$ is the outer expectation, which equals the ordinary expectation whenever they are measurable. Both are bounded by $2T$ in absolute value, so the measurable cover attains the outer expectation.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.2, p.8 (PDF 8); Theorem 5.1, p.22 (PDF 22); Definition 2.2, p.8

import Mathlib
import Definitions.Def_CalibeatBandit_Supplement_PricingRun

set_option autoImplicit false

universe u

namespace CalibeatBandit

namespace Supplement

open MeasureTheory

/-- **Outer expectation bound** `E*[f] ≤ b`: some integrable `g` dominates `f` almost surely and
has `E[g] ≤ b`. For an integrable `f` this is `E[f] ≤ b`; for a bounded `f` it is the bound on the
outer integral (the measurable cover attains the infimum). -/
def OuterExpLE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (b : ℝ) : Prop :=
  ∃ g : Ω → ℝ, Integrable g P ∧ f ≤ᵐ[P] g ∧ ∫ ω, g ω ∂P ≤ b

/-- **Regret bounds of a dynamic pricing algorithm.** For `K`-sparse recommendations and
non-increasing demands, the seller's algorithm satisfies `E[SR_T] ≤ a` and `E[Rec_T] ≤ b`: for
every common set of at most `K` recommended prices `S ⊆ [0, 1]`, every probability space
(`Ω : Type u`) and every run of the pricing protocol with production cost `c`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.2, p.8 and
Theorem 5.1, p.22.

**Formalization Note.** `SR_T` and `Rec_T` are suprema over uncountably many maps `σ`, so their
measurability is not automatic; `E` is the outer expectation (`OuterExpLE`), which is the
ordinary expectation whenever they are measurable. -/
def PricingRegretBound (K T : ℕ) (c a b : ℝ) (seller : PricingPolicy) : Prop :=
  ∀ S : Fin K → ℝ, (∀ k, S k ∈ Set.Icc (0 : ℝ) 1) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : PricingRun K T c S P seller),
    OuterExpLE P (fun ω => pricingSR T c (fun t => run.D t ω) (fun t => run.price t ω)) a ∧
    OuterExpLE P (fun ω => pricingRec T c (fun t => run.D t ω) (fun t => S (run.J t ω))
      (fun t => run.price t ω)) b

end Supplement

end CalibeatBandit


