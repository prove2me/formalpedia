-- Prove2me | Definitions.Def_MechanismDesign_Auctions_Model
-- name    : MechanismDesign_Auctions_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T23:25:07.249984+00:00
-- url     : https://prove2.me/theorems/c87eb6ef-6c22-4d56-97ba-aa677f5bc5be
-- title:
--   Single-unit auctions with independent private values: prior, virtual valuations, direct mechanisms, interim quantities, IC, IR, revenue, welfare
-- statement:
--   This file sets up the single-unit auction model of Börgers, §3.2.1–3.2.5.
--
--   **Environment.** There are $N \ge 2$ potential buyers $i \in I$. Buyer $i$'s valuation $\theta_i$ is a random variable with density $f_i$ on the common support $[\underline\theta, \bar\theta]$, where $0 \le \underline\theta < \bar\theta$; each $f_i$ is measurable, integrable, strictly positive on $[\underline\theta,\bar\theta]$ and integrates to $1$ there. Valuations are independent, so the type vector $\theta$ has the product law $F$ on $\Theta = [\underline\theta,\bar\theta]^N$ with density
--   $$f(\theta) = \prod_{i \in I} f_i(\theta_i).$$
--   The cumulative distribution function is $F_i(\theta_i) = \int_{\underline\theta}^{\theta_i} f_i(x)\,dx$ and the **virtual valuation** (Eq. (3.6)) is
--   $$\psi_i(\theta_i) = \theta_i - \frac{1 - F_i(\theta_i)}{f_i(\theta_i)}.$$
--   The environment is **regular** (Assumption 3.1) if every $\psi_i$ is strictly increasing on $[\underline\theta,\bar\theta]$.
--
--   **Direct mechanisms** (Definition 3.1). A direct mechanism consists of an allocation rule $q$ and payment rules $t_i$, where at every $\theta \in \Theta$ the vector $q(\theta) = (q_1(\theta),\dots,q_N(\theta))$ lies in $\Delta = \{(q_1,\dots,q_N) : 0 \le q_i \le 1,\ \sum_i q_i \le 1\}$ and $t_i(\theta) \in \mathbb R$ is buyer $i$'s payment. A mechanism is *well defined* if $q_i$ and $t_i$ are measurable, $t_i$ is integrable, and for every $\theta_i$ the map $\theta_{-i} \mapsto t_i(\theta_i,\theta_{-i})$ is integrable.
--
--   **Interim quantities** (Eqs. (3.1)–(3.2)):
--   $$Q_i(\theta_i) = \int_{\Theta_{-i}} q_i(\theta_i,\theta_{-i}) f_{-i}(\theta_{-i})\,d\theta_{-i},\qquad T_i(\theta_i) = \int_{\Theta_{-i}} t_i(\theta_i,\theta_{-i}) f_{-i}(\theta_{-i})\,d\theta_{-i},$$
--   and $U_i(\theta_i) = \theta_i Q_i(\theta_i) - T_i(\theta_i)$.
--
--   **Constraints.** The mechanism is *incentive-compatible* (Definition 3.2) if $\theta_i Q_i(\theta_i) - T_i(\theta_i) \ge \theta_i Q_i(\theta_i') - T_i(\theta_i')$ for all $i$ and $\theta_i,\theta_i' \in [\underline\theta,\bar\theta]$, and *individually rational* (Definition 3.3) if $U_i(\theta_i) \ge 0$ for all $i$ and $\theta_i$. The comparison class of the chapter ("admissible") is the set of well-defined, incentive-compatible, individually rational direct mechanisms.
--
--   **Objectives.** Expected revenue is $\mathbb E\big[\sum_i t_i(\theta)\big]$; expected welfare (Eq. (3.8)) is $\mathbb E\big[\sum_i q_i(\theta)\theta_i\big]$.
--
--   **Allocation rules.** Myerson's rule (Eq. (3.7)) gives the good to $i$, $q_i(\theta) = 1$, if $\psi_i(\theta_i) > 0$ and $\psi_i(\theta_i) > \psi_j(\theta_j)$ for all $j \ne i$, and sets $q_i(\theta)=0$ otherwise. The efficient rule sets $q_i(\theta) = 1$ if $\theta_i > \theta_j$ for all $j \ne i$ and $0$ otherwise.
--
--   These objects are the vocabulary of the revelation principle, the envelope characterization of Bayesian incentive compatibility, and Myerson's optimal auction.
--
--   **Formalization Note** Buyers are a finite type `ι` with at least two elements. The prior is the measure on `ι → ℝ` with density $\prod_i f_i(\theta_i)$ with respect to Lebesgue measure restricted to $\Theta$. The interim expectation over $\theta_{-i}$ is written as the prior expectation of $q_i$ (or $t_i$) with the $i$-th coordinate replaced by $\theta_i$ (`Function.update`); since coordinates are independent this is the book's integral against $f_{-i}$. Allocation and payment rules are total functions on `ι → ℝ` but only their values on $\Theta$ matter; feasibility is required on $\Theta$. Measurability and integrability are the book's implicit convention (note 2 of Chapter 2, p.235: "We omit measurability requirements throughout this text").
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.32–42, §3.2.1 (setup), Definition 3.1 (p.34), Eqs. (3.1)–(3.2) (pp.35–36), Definitions 3.2–3.3 (p.36), Eqs. (3.6)–(3.7) (p.40), Assumption 3.1 (p.41), Eq. (3.8) (p.42)

import Mathlib

open MeasureTheory

namespace MechanismDesign.Auctions

/-- The independent-private-values environment of Börgers §3.2.1 (p.32): buyers `ι` (at least
two), a common type interval `[lo, hi]` with `0 ≤ lo < hi`, and for every buyer `i` a density
`f i` of the valuation `θ_i`, strictly positive on `[lo, hi]` and integrating to `1` there.
Valuations are independent, so the joint density on `Θ = [lo, hi]^ι` is `∏ i, f i (θ i)`. -/
structure Environment (ι : Type*) [Fintype ι] where
  /-- the lower end `θ̲` of the common support -/
  lo : ℝ
  /-- the upper end `θ̄` of the common support -/
  hi : ℝ
  /-- the density `f_i` of buyer `i`'s valuation -/
  f : ι → ℝ → ℝ
  two_le_card : 2 ≤ Fintype.card ι
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  f_measurable : ∀ i, Measurable (f i)
  f_pos : ∀ i, ∀ x ∈ Set.Icc lo hi, 0 < f i x
  f_intervalIntegrable : ∀ i, IntervalIntegrable (f i) volume lo hi
  f_integral : ∀ i, ∫ x in lo..hi, f i x = 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The type space `Θ = [θ̲, θ̄]^N`. -/
def Environment.typeSpace (E : Environment ι) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc E.lo E.hi)

/-- The common prior `F = ∏ F_i`: the law on `ι → ℝ` with density `θ ↦ ∏ i, f_i(θ_i)` on `Θ`
(and no mass outside `Θ`). -/
noncomputable def Environment.prior (E : Environment ι) : Measure (ι → ℝ) :=
  (volume.restrict E.typeSpace).withDensity (fun θ => ∏ i, ENNReal.ofReal (E.f i (θ i)))

/-- The cumulative distribution function `F_i(θ_i) = ∫_{θ̲}^{θ_i} f_i(x) dx`. -/
noncomputable def Environment.cdf (E : Environment ι) (i : ι) (x : ℝ) : ℝ :=
  ∫ y in E.lo..x, E.f i y

/-- The virtual valuation, Eq. (3.6): `ψ_i(θ_i) = θ_i − (1 − F_i(θ_i)) / f_i(θ_i)`. -/
noncomputable def Environment.virtualValue (E : Environment ι) (i : ι) (x : ℝ) : ℝ :=
  x - (1 - E.cdf i x) / E.f i x

/-- Regularity, Assumption 3.1 (p.41): every `ψ_i` is strictly increasing on `[θ̲, θ̄]`. -/
def Environment.Regular (E : Environment ι) : Prop :=
  ∀ i, StrictMonoOn (E.virtualValue i) (Set.Icc E.lo E.hi)

/-- A direct mechanism, Definition 3.1 (p.34): an allocation rule `q` with values in
`Δ = {(q_1,…,q_N) | 0 ≤ q_i ≤ 1, ∑ q_i ≤ 1}` on `Θ`, and payment rules `t_i : Θ → ℝ`.
Both are total functions on `ι → ℝ`; only their values on `Θ` matter. -/
structure DirectMechanism (E : Environment ι) where
  /-- `q i θ` is the probability that buyer `i` gets the good at the report profile `θ` -/
  q : ι → (ι → ℝ) → ℝ
  /-- `t i θ` is buyer `i`'s payment to the seller at the report profile `θ` -/
  t : ι → (ι → ℝ) → ℝ
  q_nonneg : ∀ θ ∈ E.typeSpace, ∀ i, 0 ≤ q i θ
  q_le_one : ∀ θ ∈ E.typeSpace, ∀ i, q i θ ≤ 1
  sum_q_le_one : ∀ θ ∈ E.typeSpace, ∑ i, q i θ ≤ 1

variable {E : Environment ι}

/-- The measurability and integrability the book leaves implicit (Ch. 2 note 2, p.235; Ch. 3
note 1): `q_i`, `t_i` are measurable, `t_i` is integrable under the prior, and so is every section
`θ_{-i} ↦ t_i(θ_i, θ_{-i})`, so that the interim payment `T_i(θ_i)` is a genuine expectation. -/
structure DirectMechanism.WellDefined (m : DirectMechanism E) : Prop where
  q_measurable : ∀ i, Measurable (m.q i)
  t_measurable : ∀ i, Measurable (m.t i)
  t_integrable : ∀ i, Integrable (m.t i) E.prior
  t_section_integrable : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
    Integrable (fun θ => m.t i (Function.update θ i x)) E.prior

/-- Interim allocation probability, Eq. (3.1):
`Q_i(θ_i) = ∫_{Θ_{-i}} q_i(θ_i, θ_{-i}) f_{-i}(θ_{-i}) dθ_{-i}`, written as the prior expectation
of `q_i` with the `i`-th coordinate replaced by `θ_i`. -/
noncomputable def DirectMechanism.interimQ (m : DirectMechanism E) (i : ι) (x : ℝ) : ℝ :=
  ∫ θ, m.q i (Function.update θ i x) ∂E.prior

/-- Interim expected payment, Eq. (3.2). -/
noncomputable def DirectMechanism.interimT (m : DirectMechanism E) (i : ι) (x : ℝ) : ℝ :=
  ∫ θ, m.t i (Function.update θ i x) ∂E.prior

/-- Interim expected utility `U_i(θ_i) = θ_i Q_i(θ_i) − T_i(θ_i)` (p.36). -/
noncomputable def DirectMechanism.interimU (m : DirectMechanism E) (i : ι) (x : ℝ) : ℝ :=
  x * m.interimQ i x - m.interimT i x

/-- Bayesian incentive compatibility, Definition 3.2 (p.36). -/
def DirectMechanism.IsIC (m : DirectMechanism E) : Prop :=
  ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ x' ∈ Set.Icc E.lo E.hi,
    x * m.interimQ i x' - m.interimT i x' ≤ x * m.interimQ i x - m.interimT i x

/-- Interim individual rationality, Definition 3.3 (p.36). -/
def DirectMechanism.IsIR (m : DirectMechanism E) : Prop :=
  ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, 0 ≤ m.interimU i x

/-- The seller's expected revenue `E[∑_i t_i(θ)]`. -/
noncomputable def DirectMechanism.revenue (m : DirectMechanism E) : ℝ :=
  ∑ i, ∫ θ, m.t i θ ∂E.prior

/-- Expected utilitarian welfare `E[∑_i q_i(θ) θ_i]`, Eq. (3.8) (p.42). -/
noncomputable def DirectMechanism.welfare (m : DirectMechanism E) : ℝ :=
  ∫ θ, ∑ i, m.q i θ * θ i ∂E.prior

/-- The comparison class of §3.2.4–3.2.5: well-defined, incentive-compatible and individually
rational direct mechanisms. -/
def DirectMechanism.Admissible (m : DirectMechanism E) : Prop :=
  m.WellDefined ∧ m.IsIC ∧ m.IsIR

/-- Myerson's allocation rule, Eq. (3.7) / Proposition 3.4 (i): the good goes to `i` iff
`ψ_i(θ_i) > 0` and `ψ_i(θ_i) > ψ_j(θ_j)` for every `j ≠ i`; otherwise `q_i(θ) = 0`. -/
noncomputable def Environment.myersonAlloc (E : Environment ι) (i : ι) (θ : ι → ℝ) : ℝ := by
  classical
  exact if 0 < E.virtualValue i (θ i) ∧ ∀ j, j ≠ i → E.virtualValue j (θ j) < E.virtualValue i (θ i)
    then 1 else 0

/-- The efficient allocation rule, Proposition 3.5 (i): the good goes to `i` iff `θ_i > θ_j`
for every `j ≠ i`; otherwise `q_i(θ) = 0`. -/
noncomputable def efficientAlloc (i : ι) (θ : ι → ℝ) : ℝ := by
  classical
  exact if ∀ j, j ≠ i → θ j < θ i then 1 else 0

end MechanismDesign.Auctions


