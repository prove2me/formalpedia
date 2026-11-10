-- Prove2me | Definitions.Def_BilatMatch_priorClasses
-- name    : BilatMatch_priorClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:13:32.335205+00:00
-- url     : https://prove2.me/theorems/1d5c8349-8f1b-461d-a156-b1c34f50c552
-- title:
--   Natural report domains and the prior classes $\mathfrak S_\alpha$, $\mathfrak B$
-- statement:
--   The **natural report domain** of an auxiliary-market agent is the finite ordered support of a finitely supported prior, or the support interval $[\underline c,\bar c]$ of a regular interval-support seller.
--
--   For $\alpha\ge0$, $\mathfrak S_\alpha$ is a class of bounded seller priors, each with finite support or regular with interval support as in §3.2, **preserved by full-prior regularization followed by conditioning on any positive-mass initial cap**: if $F_S\in\mathfrak S_\alpha$ and $\kappa$ is an initial cap with $\hat F_S(\kappa)>0$, the conditional prior $\hat F_S(\cdot\mid\kappa)$ is in $\mathfrak S_\alpha$. $\mathfrak B$ is a class of finite buyer priors **closed under strictly positive reweighting on each fixed support**: every finitely supported prior with the same support as a member is a member.
--
--   **Formalization Note** Conditioning is Mathlib's conditional measure $F(\cdot\mid\kappa)=F(\kappa)^{-1}F|_\kappa$. Caps are lower sets of $\mathbb R$; for a prior carried by its domain this gives the same conditional priors as initial subsets of the domain.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), p.14 (pdf p.16), before Lemma 3.8; §3.1, p.8 (pdf p.10)

import Mathlib
import Definitions.Def_BilatMatch_reconLaw
import Definitions.Def_BilatMatch_sellerCost

open MeasureTheory

namespace BilatMatch

/-!
# Natural report domains and the prior classes `𝔖_α`, `𝔅`

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), p.14 (pdf p.16), before Lemma 3.8; §3.1, p.8.

**Formalization Note**
* The report domain of an agent of an auxiliary market is its finite ordered support (the atoms of
  a finitely supported prior) or, for a regular seller with interval support `[c̲, c̄]`, the interval
  itself (`IsNaturalDomain`).
* "Conditioning on any positive-mass initial cap" uses Mathlib's conditional measure
  `ProbabilityTheory.cond F κ = F(κ)⁻¹ • F|_κ`, i.e. `F^κ(A) = F(A ∩ κ)/F(κ)` (p.10). Caps are taken
  as lower sets of `ℝ`: for a prior carried by its report domain `D`, conditioning on an initial
  subset of `D` and on its lower closure in `ℝ` give the same measure.
* "Bounded": the prior gives full mass to some interval `[−K, K]`.
-/

/-- The natural report domain of an auxiliary-market agent with prior `μ` (§3.1, p.8): the finite
ordered support, or the support interval `[c̲, c̄]` of a regular interval-support prior. -/
def IsNaturalDomain (μ : Measure ℝ) (D : Set ℝ) : Prop :=
  (IsFiniteSupport μ ∧ D = atoms μ) ∨
    ∃ lo hi f, IsRegularIntervalLaw μ lo hi f ∧ D = Set.Icc lo hi

/-- `𝔖_α` (p.14): a class of bounded seller priors, each with finite support or regular with interval
support as in §3.2, preserved by full-prior regularization followed by conditioning on any
positive-mass initial cap. -/
def IsSellerClass (α : ℝ) (𝔖 : Set (Measure ℝ)) : Prop :=
  ∀ F ∈ 𝔖, (∃ K : ℝ, F (Set.Icc (-K) K)ᶜ = 0) ∧
    (IsFiniteSupport F ∨ IsRegularIntervalSeller α F) ∧
    ∀ κ : Set ℝ, IsLowerSet κ → 0 < regularize α F κ →
      ProbabilityTheory.cond (regularize α F) κ ∈ 𝔖

/-- `𝔅` (p.14): a class of finite buyer priors closed under strictly positive reweighting on each
fixed support (every finitely supported prior with the same atoms belongs to the class). -/
def IsBuyerClass (𝔅 : Set (Measure ℝ)) : Prop :=
  ∀ F ∈ 𝔅, IsFiniteSupport F ∧ ∀ G, IsFiniteSupport G → atoms G = atoms F → G ∈ 𝔅

end BilatMatch


