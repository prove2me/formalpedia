-- Prove2me | Definitions.Def_CompetingSellers_IsPricingMech
-- name    : CompetingSellers_IsPricingMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:53.827942+00:00
-- url     : https://prove2.me/theorems/1e539958-7014-4fb8-a709-c80d656afcef
-- title:
--   The mechanism realizing a pricing function, and proper pricing mechanisms
-- statement:
--   A pricing function $P$ becomes a mechanism by implementing each available option by a lottery: the message chosen for allocation $x$ returns the good with probability $x$ and charges the deterministic payment $P(x)$. A mechanism $M$ **realizes** $P$ if every message returns such a lottery $x\,\delta_{(1,P(x))}+(1-x)\,\delta_{(0,P(x))}$ for some $x\in[0,1]$ with $P(x)<\infty$, and every such lottery is returned by some message. A **proper pricing mechanism** is a mechanism realizing a proper pricing function with $P(\bar x)<\infty$.
--
--   The paper's pricing mechanisms (fixed price $\mathrm{FP}(p)$, single lotteries $\mathrm{SL}_{x,p}$, double lotteries $\mathrm{DL}_{x,q}$, capped mechanisms) enter the game through such realizations.
--
--   **Formalization Note** Two realizations of the same $P$ have the same image, so the buyer, Bob and Alice face the same options under either.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2, p.16 (PDF 19); proof of Observation 2.2 and footnote 24, p.54

import Mathlib
import Definitions.Def_CompetingSellers_Mech
import Definitions.Def_CompetingSellers_IsProperPricing

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- The lottery giving the good with probability `x` for the deterministic payment `p`:
`x · δ_(1, p) + (1 − x) · δ_(0, p)`. -/
noncomputable def lotteryMeasure (x p : ℝ) : Measure (Bool × ℝ≥0) :=
  ENNReal.ofReal x • Measure.dirac (true, p.toNNReal) +
    ENNReal.ofReal (1 - x) • Measure.dirac (false, p.toNNReal)

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **The pricing mechanism of a pricing function** (p.16 and proof of Observation 2.2, p.54).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.16 (PDF 19): "The buyer can choose any `x ∈ [0, 1]` with
`P(x) < ∞`, make an expected payment of `P(x)`, and receive the good with probability `x`"; proof
of Observation 2.2, p.54: "Implementing each option by a Bernoulli allocation and its
deterministic payment gives a mechanism with compact image and the null option."

`IsPricingMech P M`: every message of `M` returns such a lottery `(x, P(x))` with `P(x) < ∞`,
and every such lottery is returned by some message.

**Formalization Note.** A pricing function is used as a strategy only through a mechanism
realizing it; all realizations have the same image, hence the same play. -/
def IsPricingMech (P : ℝ → ℝ≥0∞) (M : Mech S null) : Prop :=
  (∀ σ : S, ∃ x ∈ Set.Icc (0 : ℝ) 1, P x ≠ ⊤ ∧
      (M.law σ : Measure (Bool × ℝ≥0)) = lotteryMeasure x (P x).toReal) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, P x ≠ ⊤ →
      ∃ σ : S, (M.law σ : Measure (Bool × ℝ≥0)) = lotteryMeasure x (P x).toReal

/-- A **proper pricing mechanism** (Observation 2.2): a mechanism realizing a proper pricing
function with `P(x̄) < ∞`. -/
def IsPricingMechanism (M : Mech S null) : Prop :=
  ∃ P : ℝ → ℝ≥0∞, IsSellerPricing P ∧ IsPricingMech P M

end CompetingSellers


