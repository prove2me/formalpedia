-- Prove2me | Definitions.Def_MechanismDesign_DominantExamples_Auction
-- name    : MechanismDesign_DominantExamples_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:08:21.713019+00:00
-- url     : https://prove2.me/theorems/32fef0cd-d641-4a6a-b85d-bb3bc88b0e43
-- title:
--   Single unit auctions without a prior (Börgers §4.2): direct mechanisms, dominant strategy IC, ex post IR, canonical auctions
-- statement:
--   This file sets up the single unit auction model of Börgers, §4.2, in which the designer relies on no assumption about the buyers' beliefs.
--
--   **Environment.** A seller owns one indivisible good. There is a finite set $I$ of potential buyers. Buyer $i$'s type is $\theta_i \in [\underline\theta, \bar\theta]$, where $0 \le \underline\theta < \bar\theta$. We write $\Theta = [\underline\theta,\bar\theta]^I$ for the set of type vectors, $\theta_{-i}$ for $\theta$ without its $i$-th entry and $\Theta_{-i}$ for the set of such vectors. A buyer of type $\theta_i$ who obtains the good and pays $t_i$ has utility $\theta_i - t_i$; if she does not obtain the good her utility is $-t_i$.
--
--   **Direct mechanisms** (Definition 3.1). A direct mechanism $(q, t_1, \dots, t_N)$ consists of an allocation rule $q : \Theta \to \Delta$ and payment rules $t_i : \Theta \to \mathbb R$, where
--   $$\Delta = \Big\{(q_1,\dots,q_N) \;\Big|\; 0 \le q_i \le 1 \text{ for all } i,\ \sum_{i} q_i \le 1\Big\}.$$
--   Here $q_i(\theta)$ is the probability that buyer $i$ obtains the good and $t_i(\theta)$ is her payment when the reported type vector is $\theta$. Buyer $i$'s ex post utility under truthful reporting is $u_i(\theta) = \theta_i q_i(\theta) - t_i(\theta)$.
--
--   1. **Dominant strategy incentive compatibility** (Definition 4.1): for all $i$, all $\theta_i, \theta_i' \in [\underline\theta,\bar\theta]$ and all $\theta_{-i} \in \Theta_{-i}$,
--   $$\theta_i q_i(\theta_i,\theta_{-i}) - t_i(\theta_i,\theta_{-i}) \ge \theta_i q_i(\theta_i',\theta_{-i}) - t_i(\theta_i',\theta_{-i}).$$
--   2. **Ex post individual rationality** (Definition 4.2): $\theta_i q_i(\theta) - t_i(\theta) \ge 0$ for all $i$ and all $\theta \in \Theta$.
--   3. **Canonical auction** (Definition 4.3): there are strictly increasing and continuous functions $\psi_i : [\underline\theta,\bar\theta] \to \mathbb R$ such that for all $\theta \in \Theta$ and all $i$,
--   $$q_i(\theta) = \begin{cases} \tfrac1n & \text{if } \psi_i(\theta_i) \ge 0 \text{ and } \psi_i(\theta_i) \ge \psi_j(\theta_j) \text{ for all } j \ne i,\\ 0 & \text{otherwise,}\end{cases}$$
--   where $n$ is the number of agents $k$ with $\psi_k(\theta_k) = \psi_i(\theta_i)$, and
--   $$t_i(\theta) = \begin{cases} \tfrac1n \min\{\hat\theta_i \in [\underline\theta,\bar\theta] \mid q_i(\hat\theta_i,\theta_{-i}) > 0\} & \text{if } q_i(\theta) > 0,\\ 0 & \text{if } q_i(\theta) = 0.\end{cases}$$
--
--   These are the objects every result of §4.2 is stated in terms of. With $\psi_i(\theta_i) = \theta_i$ a canonical auction is the second price auction; with $\psi_i$ the virtual valuations of §3.2 it is Myerson's optimal auction.
--
--   **Formalization Note** Buyers form a finite type `ι` with decidable equality. The pair $(\theta_i', \theta_{-i})$ is written `Function.update θ i x` for a type vector `θ ∈ Θ`; the $i$-th coordinate of `θ` is then irrelevant, so quantifying over `θ ∈ Θ` quantifies over $\theta_{-i} \in \Theta_{-i}$. The constraints $q(\theta) \in \Delta$ are imposed on $\Theta$ only. The minimum in the canonical payment is written as an infimum (`sInf`); whenever $q_i(\theta) > 0$ the set is nonempty and, because $\psi_i$ is continuous and strictly increasing, closed, so the infimum is attained, as the book notes on p.83. No measurability is needed: nothing in §4.2 is integrated except a monotone function of one variable.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.78–82: setup §4.2.1 pp.78–79; Definition 3.1 and Δ p.34; Definitions 4.1–4.2 p.80; Definition 4.3 p.82

import Mathlib

namespace MechanismDesign.DominantExamples

/-- The single unit auction environment of Börgers, *An Introduction to the Theory of Mechanism
Design*, §4.2.1 (pp.78–79): every buyer's type lies in the common interval `[θ̲, θ̄]` with
`0 ≤ θ̲ < θ̄`. No prior over types is assumed in Chapter 4. -/
structure AuctionSetting where
  /-- lower end `θ̲` of the type interval -/
  lo : ℝ
  /-- upper end `θ̄` of the type interval -/
  hi : ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi

namespace AuctionSetting

/-- The set of type vectors `Θ = [θ̲, θ̄]^I`. -/
def typeSpace (E : AuctionSetting) (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ => Set.Icc E.lo E.hi

end AuctionSetting

/-- A direct mechanism for the single unit auction (Definition 3.1, p.34, used in §4.2.2):
an allocation rule `q : Θ → Δ`, where `Δ` is the set of vectors `(q_1, …, q_N)` with
`0 ≤ q_i ≤ 1` and `∑_i q_i ≤ 1` (`q i θ` is the probability that buyer `i` obtains the good),
and payment rules `t_i : Θ → ℝ` (`t i θ` is buyer `i`'s transfer to the seller). The
constraints are imposed on `Θ` only; values outside `Θ` play no role. -/
structure AuctionMechanism (E : AuctionSetting) (ι : Type*) [Fintype ι] where
  /-- allocation rule: `q i θ` is the probability that buyer `i` gets the good -/
  q : ι → (ι → ℝ) → ℝ
  /-- payment rule: `t i θ` is the payment of buyer `i` -/
  t : ι → (ι → ℝ) → ℝ
  q_nonneg : ∀ θ ∈ E.typeSpace ι, ∀ i, 0 ≤ q i θ
  q_le_one : ∀ θ ∈ E.typeSpace ι, ∀ i, q i θ ≤ 1
  sum_q_le_one : ∀ θ ∈ E.typeSpace ι, ∑ i, q i θ ≤ 1

namespace AuctionMechanism

variable {E : AuctionSetting} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Buyer `i`'s ex post utility under truthful reporting at the type vector `θ`:
`u_i(θ) = θ_i q_i(θ) − t_i(θ)`. -/
def u (M : AuctionMechanism E ι) (i : ι) (θ : ι → ℝ) : ℝ :=
  θ i * M.q i θ - M.t i θ

/-- Definition 4.1 (p.80), dominant strategy incentive compatibility: for all `i`, all
`θ_i, θ_i' ∈ [θ̲, θ̄]` and all `θ_{-i} ∈ Θ_{-i}`,
`θ_i q_i(θ_i, θ_{-i}) − t_i(θ_i, θ_{-i}) ≥ θ_i q_i(θ_i', θ_{-i}) − t_i(θ_i', θ_{-i})`.
The pair `(θ_i, θ_{-i})` is the type vector `θ ∈ Θ`; `(θ_i', θ_{-i})` is
`Function.update θ i x`. -/
def IsDSIC (M : AuctionMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, ∀ x ∈ Set.Icc E.lo E.hi,
    θ i * M.q i (Function.update θ i x) - M.t i (Function.update θ i x) ≤
      θ i * M.q i θ - M.t i θ

/-- Definition 4.2 (p.80), ex post individual rationality: for all `i` and all `θ ∈ Θ`,
`θ_i q_i(θ) − t_i(θ) ≥ 0`. -/
def IsEPIR (M : AuctionMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, 0 ≤ θ i * M.q i θ - M.t i θ

end AuctionMechanism

open Classical in
/-- The number `n` of agents `k` with `ψ_k(θ_k) = ψ_i(θ_i)` (Definition 4.3, p.82); it counts
`i` itself, so it is at least `1`. -/
noncomputable def tieCount {ι : Type*} [Fintype ι] (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) : ℕ :=
  (Finset.univ.filter fun k => ψ k (θ k) = ψ i (θ i)).card

open Classical in
/-- The allocation rule of a canonical auction (Definition 4.3, p.82):
`q_i(θ) = 1/n` if `ψ_i(θ_i) ≥ 0` and `ψ_i(θ_i) ≥ ψ_j(θ_j)` for all `j ≠ i`, where `n` is the
number of agents `k` with `ψ_k(θ_k) = ψ_i(θ_i)`; `q_i(θ) = 0` otherwise. -/
noncomputable def canonicalAuctionQ {ι : Type*} [Fintype ι] (ψ : ι → ℝ → ℝ) (i : ι)
    (θ : ι → ℝ) : ℝ :=
  if 0 ≤ ψ i (θ i) ∧ ∀ j, j ≠ i → ψ j (θ j) ≤ ψ i (θ i) then
    1 / (tieCount ψ θ i : ℝ)
  else 0

open Classical in
/-- The payment rule of a canonical auction (Definition 4.3, p.82):
`t_i(θ) = (1/n) · min {θ̂_i ∈ [θ̲, θ̄] | q_i(θ̂_i, θ_{-i}) > 0}` if `q_i(θ) > 0`, and
`t_i(θ) = 0` if `q_i(θ) = 0`. The minimum is written as `sInf`; when `q_i(θ) > 0` the set
contains `θ_i` and, for continuous strictly increasing `ψ_i`, is a closed subinterval of
`[θ̲, θ̄]`, so the infimum is attained. -/
noncomputable def canonicalAuctionT {ι : Type*} [Fintype ι] [DecidableEq ι] (E : AuctionSetting)
    (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) : ℝ :=
  if 0 < canonicalAuctionQ ψ i θ then
    (1 / (tieCount ψ θ i : ℝ)) *
      sInf {x | x ∈ Set.Icc E.lo E.hi ∧ 0 < canonicalAuctionQ ψ i (Function.update θ i x)}
  else 0

/-- Definition 4.3 (p.82), canonical auction: there are strictly increasing and continuous
functions `ψ_i : [θ̲, θ̄] → ℝ` such that for all `θ ∈ Θ` and all `i` the allocation and the
payment of the mechanism are `canonicalAuctionQ ψ i θ` and `canonicalAuctionT E ψ i θ`. -/
def AuctionMechanism.IsCanonical {E : AuctionSetting} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : AuctionMechanism E ι) : Prop :=
  ∃ ψ : ι → ℝ → ℝ,
    (∀ i, StrictMonoOn (ψ i) (Set.Icc E.lo E.hi) ∧ ContinuousOn (ψ i) (Set.Icc E.lo E.hi)) ∧
    ∀ θ ∈ E.typeSpace ι, ∀ i,
      M.q i θ = canonicalAuctionQ ψ i θ ∧ M.t i θ = canonicalAuctionT E ψ i θ

end MechanismDesign.DominantExamples


