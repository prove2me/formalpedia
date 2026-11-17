-- Prove2me | Definitions.Def_ValiantModel_Supplement_GeneralModel
-- name    : ValiantModel_Supplement_GeneralModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:20.544054+00:00
-- url     : https://prove2.me/theorems/a34e94c2-71be-44ae-a0b2-6631fd4ceb5b
-- title:
--   Definition 3 — learnability in Valiant's model over a general domain $X$
-- statement:
--   Fix a domain $X$ and a concept class $H\subseteq\{0,1\}^X$. A learner interacts with two oracles: the **example oracle**, which returns an independent draw $x\sim D$ from an unknown distribution $D$ over $X$, and the **membership oracle**, which answers a query $x\in X$ with $h^\star(x)$ for the unknown target $h^\star\in H$. The distribution is **compatible** with $h^\star$ if $D(\mathrm{supp}(h^\star))=1$.
--
--   A deterministic learner is a protocol: at each step it either outputs a hypothesis $g:X\to\{0,1\}$, or calls the example oracle and continues on the point seen, or queries a point of $X$ and continues on the answer. A randomized learner draws its internal randomness from a probability space first and then runs a deterministic protocol. The learner uses $m$ positive examples and $q$ membership queries if, for every value of its randomness, every path of its protocol makes at most $m$ example calls and at most $q$ queries.
--
--   The output $g$ **meets the Valiant conditions** for $(h^\star,D,\varepsilon)$ if
--   $$\mathrm{supp}(g)\subseteq\mathrm{supp}(h^\star)\qquad\text{and}\qquad \Pr_{x\sim D}\big(x\notin\mathrm{supp}(g)\big)\le\varepsilon .$$
--
--   $H$ is **learnable in Valiant's model over $X$** if there are a learner and $m:(0,1)^2\to\mathbb N$ such that for every target $h^\star\in H$, every distribution $D$ over $X$ compatible with $h^\star$ and every $\varepsilon,\delta\in(0,1)$, the learner on input $(\varepsilon,\delta)$, using $m(\varepsilon,\delta)$ positive examples and $m(\varepsilon,\delta)$ membership queries, outputs with probability at least $1-\delta$ a hypothesis meeting the Valiant conditions.
--
--   This is the general-domain model of Theorems 1.5, 1.6, 5.2, 5.4 and A.1. Some of those theorems give separate example and query budgets, so the definition also records the predicate "learns $H$ with $m(\varepsilon,\delta)$ examples and $q(\varepsilon,\delta)$ queries".
--
--   **Formalization Note** The domain is a measurable space and a distribution is a probability measure on it. The abstract-domain theorems use the discrete σ-algebra, where every subset is an event; $\mathbb R^d$ uses the Borel σ-algebra. Compatibility is "$h^\star(x)=1$ almost surely". The error of an output is measured with the measure's outer measure, so it is defined for every output. The success probability is defined by recursion on the protocol, using the lower Lebesgue integral over each example draw and over the internal randomness. This is the exact probability whenever the success event is measurable, which on a discrete domain it always is in the draws. The internal randomness is an arbitrary probability space, examples and queries interleave freely, queries may be asked anywhere in $X$, and the output is arbitrary (improper). Depths are counted in $\mathbb N\cup\{\infty\}$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Definition 3, p.5 (PDF p.7); Definitions 4–6, p.14 (PDF p.16)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ValiantModel.Supplement

/-- A deterministic interaction of a learner with the example oracle and the membership oracle
(Definitions 5 and 6) over an arbitrary domain `X`, for **Definition 3 (Valiant's Model over a General
Domain)** of Hanneke, Mehrotra, Velegkas, Zampetakis, *What is Learnable in Valiant's Theory of the
Learnable?*, arXiv:2605.13840 (version held, sha256 f793f255…), p.5 (PDF p.7), and Definitions 5, 6,
p.14 (PDF p.16): stop and output a hypothesis `X → Bool`, call the example oracle and continue on the
point seen, or query any point of `X` and continue on the answer.

**Formalization Note.** Examples and queries interleave freely, each step may depend on everything
seen before (adaptive), any point of `X` may be queried, and the output is any function `X → Bool`
(improper). The tree takes neither the target nor the distribution as an argument. -/
inductive GProtocol (X : Type) : Type
  | output (g : X → Bool) : GProtocol X
  | example (k : X → GProtocol X) : GProtocol X
  | query (x : X) (k : Bool → GProtocol X) : GProtocol X

namespace GProtocol

variable {X : Type}

/-- The largest number of example-oracle calls on any path of the protocol (in `ℕ∞`, since the
domain may be infinite). -/
noncomputable def exampleDepth : GProtocol X → ℕ∞
  | output _ => 0
  | «example» k => 1 + ⨆ x, exampleDepth (k x)
  | query _ k => max (exampleDepth (k false)) (exampleDepth (k true))

/-- The largest number of membership queries on any path of the protocol. -/
noncomputable def queryDepth : GProtocol X → ℕ∞
  | output _ => 0
  | «example» k => ⨆ x, queryDepth (k x)
  | query _ k => 1 + max (queryDepth (k false)) (queryDepth (k true))

end GProtocol

/-- **Definition 4 (Compatibility)**, arXiv:2605.13840 (version held), p.14 (PDF p.16), over a general
domain: a draw from `D` is positive for `h` almost surely. -/
def GCompatible {X : Type} [MeasurableSpace X] (D : Measure X) (h : X → Bool) : Prop :=
  ∀ᵐ x ∂D, h x = true

/-- The success conditions of Definition 3, arXiv:2605.13840 (version held), p.5 (PDF p.7), for an
output `g`, target `h`, distribution `D` and error `ε`: `supp(g) ⊆ supp(h)` and
`Pr_{x∼D}(x ∉ supp(g)) ≤ ε`.

**Formalization Note.** `D` applied to a set is its outer measure, so the error is defined for every
output, measurable or not; on a discrete measurable space it is the exact probability. -/
def GMeetsValiant {X : Type} [MeasurableSpace X] (h : X → Bool) (D : Measure X) (ε : ℝ)
    (g : X → Bool) : Prop :=
  (∀ x, g x = true → h x = true) ∧ D {x | g x = false} ≤ ENNReal.ofReal ε

namespace GProtocol

variable {X : Type} [MeasurableSpace X]

/-- The probability that a deterministic protocol, run against the example oracle for `D` (fresh
independent draws) and the membership oracle for `h`, outputs a hypothesis meeting the conditions of
Definition 3 with error `ε`.

**Formalization Note.** Defined by recursion on the protocol. An example call integrates over the
draw with the lower Lebesgue integral `∫⁻`, which is the exact expectation for measurable integrands
(every integrand on a discrete measurable space) and never exceeds it otherwise. -/
noncomputable def succ (h : X → Bool) (D : Measure X) (ε : ℝ) : GProtocol X → ℝ≥0∞
  | output g => open Classical in if GMeetsValiant h D ε g then 1 else 0
  | «example» k => ∫⁻ x, succ h D ε (k x) ∂D
  | query x k => succ h D ε (k (h x))

end GProtocol

/-- A randomized learner's behaviour on one input `(ε, δ)`: internal randomness drawn from an arbitrary
probability space `(Ω, P)`, independent of the samples, followed by the deterministic protocol
`run ω` (p.15, PDF p.17: "we condition on their internal randomness"). -/
structure RandProtocol (X : Type) : Type 1 where
  Ω : Type
  [instΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  run : Ω → GProtocol X

attribute [instance] RandProtocol.instΩ RandProtocol.isProb

namespace RandProtocol

variable {X : Type}

/-- The success probability of a randomized learner against target `h` and distribution `D`.

**Formalization Note.** The lower integral over the internal randomness: the exact probability for
every learner whose success is measurable in its randomness, and a lower bound otherwise. -/
noncomputable def successProb [MeasurableSpace X] (A : RandProtocol X) (h : X → Bool)
    (D : Measure X) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (A.run ω).succ h D ε ∂A.P

/-- The budget: for every value of the internal randomness, at most `m` example-oracle calls and at
most `q` membership queries on every path. -/
def WithinBudget (A : RandProtocol X) (m q : ℕ) : Prop :=
  ∀ ω, (A.run ω).exampleDepth ≤ m ∧ (A.run ω).queryDepth ≤ q

end RandProtocol

/-- **The guarantee of Definition 3**, arXiv:2605.13840 (version held), p.5 (PDF p.7), at one
`(ε, δ)`: for every target `h ∈ H` and every probability distribution `D` over `X` compatible with
`h`, the success probability is at least `1 - δ`. -/
def GGuarantee {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (A : RandProtocol X)
    (ε δ : ℝ) : Prop :=
  ∀ h ∈ H, ∀ D : Measure X, IsProbabilityMeasure D → GCompatible D h →
    ENNReal.ofReal (1 - δ) ≤ A.successProb h D ε

/-- `L` learns `H` in Valiant's model over `X` (Definition 3) with `m(ε, δ)` positive examples and
`q(ε, δ)` membership queries: for all `ε, δ ∈ (0,1)`, `L ε δ` stays within the budget and meets the
guarantee. The budgets depend only on `(ε, δ)`. -/
def GHasComplexity {X : Type} [MeasurableSpace X] (H : Set (X → Bool))
    (L : ℝ → ℝ → RandProtocol X) (m q : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    (L ε δ).WithinBudget (m ε δ) (q ε δ) ∧ GGuarantee H (L ε δ) ε δ

/-- **Definition 3 (Valiant's Model over a General Domain)**, arXiv:2605.13840 (version held), p.5
(PDF p.7): `H ⊆ {0,1}^X` is learnable if there are a learner and `m : (0,1)² → ℕ` such that the
learner, using `m(ε, δ)` positive examples and `m(ε, δ)` membership queries, meets the guarantee.

**Formalization Note.** The budget `m(ε, δ)` bounds each oracle separately, as in the proof of
Theorem 5.2 (p.34, PDF p.36: "budget M for each oracle"). No bound on `m` is required. -/
def GLearnable {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) : Prop :=
  ∃ (L : ℝ → ℝ → RandProtocol X) (m : ℝ → ℝ → ℕ), GHasComplexity H L m m

end ValiantModel.Supplement


