-- Prove2me | Definitions.Def_CompetingSellers_Mech
-- name    : CompetingSellers_Mech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:10.899673+00:00
-- url     : https://prove2.me/theorems/b8df55a4-82b5-4c66-8bd4-a96f2254ff10
-- title:
--   Mechanism $M:\Sigma\to\Delta(\{0,1\}\times\mathbb R_{\ge0})$ with compact image and a null message
-- statement:
--   A **mechanism** of a seller takes a message $\sigma\in\Sigma$ from the buyer and returns a probability distribution $M(\sigma)$ over outcomes $(q,t)\in O=\{0,1\}\times\mathbb R_{\ge0}$, where $q=1$ means that the buyer receives the seller's good and $t$ is the transfer from the buyer to the seller. Formally $M:\Sigma\to\Delta(O)$ is measurable, its image $\{M(\sigma):\sigma\in\Sigma\}$ is compact for the topology of weak convergence, and the null message $\varnothing$ (non-participation) returns the outcome $(0,0)$ with certainty.
--
--   For a message $\sigma$ write $x(\sigma)=\mathbb E_{M(\sigma)}[q]$ for its allocation probability and $p(\sigma)=\mathbb E_{M(\sigma)}[t]\in[0,\infty]$ for its expected payment. A mechanism has a **finite menu** if it offers finitely many distinct options $(x(\sigma),p(\sigma))$ (footnote 6: "requiring infinitely many menu options means that no finite menu attains Alice's exact optimum").
--
--   This is the strategy space of both sellers in the main model; every result of the mission is about these general mechanisms.
--
--   **Formalization Note** The message space $\Sigma$ is a type `S` with a distinguished element `null`; the standing assumptions that $\Sigma$ is an uncountable standard Borel space are hypotheses of the theorems. Outcomes are `Bool × ℝ≥0`; $\Delta(O)$ is `ProbabilityMeasure` with Mathlib's weak-convergence topology and the Giry σ-algebra. Expected payments are lower integrals in $[0,\infty]$, so an infinite mean is not confused with a free option.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 Mechanisms, p.13 (PDF 16); footnote 6, p.4

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Mechanism** (§2 "Mechanisms", p.13).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), §2, p.13 (PDF 16): "A (possibly randomized) mechanism takes as
input a message `σ ∈ Σ` from the buyer, where `Σ` is an arbitrary uncountable standard Borel
message space, and samples an outcome `(q, t) ∈ O = {0, 1} × ℝ≥0` … Formally, a mechanism `M`
is then a measurable mapping `M : Σ → Δ(O)` with compact image under weak convergence of outcome
distributions. … every mechanism accepts a null message `∅`, equivalent to non-participation,
upon which the mechanism returns outcome `(0, 0)`."

**Formalization Note.** The message space `Σ` is the type `S` (the letter `Σ` is reserved in
Lean) with null message `null`; the standing assumptions that `S` is an uncountable standard Borel
space are hypotheses of the theorems, not fields here. An outcome `(q, t)` is a pair
`Bool × ℝ≥0` (`q = true` means the buyer receives the good). `Δ(O)` is
`ProbabilityMeasure (Bool × ℝ≥0)` with Mathlib's topology of weak convergence; measurability
is with respect to the Giry σ-algebra. -/
structure Mech (S : Type) [MeasurableSpace S] (null : S) where
  /-- The outcome distribution `M(σ)` returned on message `σ`. -/
  law : S → ProbabilityMeasure (Bool × ℝ≥0)
  /-- `M : Σ → Δ(O)` is measurable. -/
  measurable_law : Measurable law
  /-- The image of `M` is compact under weak convergence. -/
  isCompact_range_law : IsCompact (Set.range law)
  /-- The null message returns the outcome `(0, 0)` (no good, no transfer). -/
  law_null : (law null : Measure (Bool × ℝ≥0)) = Measure.dirac (false, 0)

namespace Mech

variable {S : Type} [MeasurableSpace S] {null : S}

/-- The allocation probability `E[q]` of message `σ`: the probability that the buyer receives
the good. -/
noncomputable def alloc (M : Mech S null) (σ : S) : ℝ :=
  ((M.law σ : Measure (Bool × ℝ≥0)) {o | o.1 = true}).toReal

/-- The expected transfer `E[t]` of message `σ`, in `ℝ≥0∞` (a distribution on `ℝ≥0` need not
have a finite mean). -/
noncomputable def pay (M : Mech S null) (σ : S) : ℝ≥0∞ :=
  ∫⁻ o, (o.2 : ℝ≥0∞) ∂(M.law σ : Measure (Bool × ℝ≥0))

/-- **Finite menu** (footnote 6, p.4): the mechanism offers finitely many distinct menu options,
an option being a lottery `(E[q], E[t])` = (allocation probability, expected payment). -/
def FiniteMenu (M : Mech S null) : Prop :=
  (Set.range fun σ => (M.alloc σ, M.pay σ)).Finite

end Mech

end CompetingSellers


