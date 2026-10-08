-- Prove2me | Definitions.Def_MechanismDesign_DominantExamples_PublicGood
-- name    : MechanismDesign_DominantExamples_PublicGood
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:08:32.853356+00:00
-- url     : https://prove2.me/theorems/7b78fabd-6151-4df9-9b36-f479aa4410be
-- title:
--   Public goods without a prior (Börgers §4.3): deterministic direct mechanisms, dominant strategy IC, ex post IR, exact budget balance, canonical mechanisms
-- statement:
--   This file sets up the public goods model of Börgers, §4.3, in which the designer relies on no assumption about the agents' beliefs.
--
--   **Environment.** A finite set $I$ of agents decides whether to produce an indivisible, nonexcludable public good, $g \in \{0,1\}$, at cost $c\,g$ with $c > 0$. Agent $i$'s type is $\theta_i \in [\underline\theta,\bar\theta]$ with $0 \le \underline\theta < \bar\theta$, and her utility from decision $g$ and transfer $t_i$ is $\theta_i g - t_i$. We write $\Theta = [\underline\theta,\bar\theta]^I$, and $\theta_{-i}$, $\Theta_{-i}$ as usual.
--
--   **Direct mechanisms** (Definition 3.4). A (deterministic) direct mechanism consists of a decision rule $q : \Theta \to \{0,1\}$ and transfer rules $t_i : \Theta \to \mathbb R$, $t_i(\theta)$ being the transfer agent $i$ makes to the community. Agent $i$'s ex post utility under truthful reporting is $u_i(\theta) = \theta_i q(\theta) - t_i(\theta)$.
--
--   1. **Dominant strategy incentive compatibility**: for all $i$, all $\theta_i,\theta_i' \in [\underline\theta,\bar\theta]$ and all $\theta_{-i} \in \Theta_{-i}$, $\ \theta_i q(\theta_i,\theta_{-i}) - t_i(\theta_i,\theta_{-i}) \ge \theta_i q(\theta_i',\theta_{-i}) - t_i(\theta_i',\theta_{-i})$.
--   2. **Ex post individual rationality**: $\theta_i q(\theta) - t_i(\theta) \ge 0$ for all $i$ and $\theta \in \Theta$.
--   3. **Ex post budget balance**, written as an equality (p.85):
--   $$\sum_{i \in I} t_i(\theta) = c\,q(\theta) \quad\text{for all } \theta \in \Theta.$$
--   4. **Canonical mechanism** (Definition 4.4): for every agent $i$ there is a strictly increasing and continuous $\psi_i : [\underline\theta,\bar\theta] \to \mathbb R$ such that for all $\theta \in \Theta$
--   $$q(\theta) = \begin{cases} 1 & \text{if } \sum_{i} \psi_i(\theta_i) \ge c,\\ 0 & \text{otherwise,}\end{cases} \qquad t_i(\theta) = \begin{cases} \min\{\hat\theta_i \in [\underline\theta,\bar\theta] \mid \psi_i(\hat\theta_i) + \sum_{j\ne i}\psi_j(\theta_j) \ge c\} & \text{if } q(\theta)=1,\\ 0 & \text{if } q(\theta) = 0.\end{cases}$$
--
--   These are the objects every result of §4.3 is stated in terms of. In contrast with Chapter 3, budget balance here is an equality: surplus funds cannot be disposed of.
--
--   **Formalization Note** Agents form a finite type `ι` with decidable equality. The decision rule is real-valued and required to take values in $\{0,1\}$ on $\Theta$. Deviations $(\theta_i',\theta_{-i})$ are `Function.update θ i x` for `θ ∈ Θ`. The minimum in the canonical transfer is written as `sInf`; when $q(\theta) = 1$ the set contains $\theta_i$ and is closed because $\psi_i$ is continuous, so the infimum is attained.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.84–87: setup §4.3.1 pp.84–85; Definition 3.4 p.47; §4.3.2 (dominant strategy IC, ex post IR, budget balance as an equality) p.85; Definition 4.4 p.87

import Mathlib

namespace MechanismDesign.DominantExamples

/-- The public goods environment of Börgers, *An Introduction to the Theory of Mechanism
Design*, §4.3.1 (pp.84–85): agents decide whether to produce an indivisible nonexcludable public
good at cost `c > 0`; every agent's type lies in `[θ̲, θ̄]` with `0 ≤ θ̲ < θ̄`, and agent `i`'s
utility from decision `g ∈ {0, 1}` and transfer `t_i` is `θ_i g − t_i`. No prior is assumed. -/
structure PublicGoodSetting where
  /-- lower end `θ̲` of the type interval -/
  lo : ℝ
  /-- upper end `θ̄` of the type interval -/
  hi : ℝ
  /-- cost `c` of producing the public good -/
  c : ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  c_pos : 0 < c

namespace PublicGoodSetting

/-- The set of type vectors `Θ = [θ̲, θ̄]^I`. -/
def typeSpace (E : PublicGoodSetting) (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ => Set.Icc E.lo E.hi

end PublicGoodSetting

/-- A deterministic direct mechanism for the public good (Definition 3.4, p.47, used in
§4.3.2): a decision rule `q : Θ → {0, 1}` and transfer rules `t_i : Θ → ℝ` (`t i θ` is the
transfer agent `i` makes to the community). The decision rule takes values in `{0, 1}` on
`Θ`; values outside `Θ` play no role. -/
structure PublicGoodMechanism (E : PublicGoodSetting) (ι : Type*) where
  /-- decision rule: `q θ = 1` if the good is produced, `0` otherwise -/
  q : (ι → ℝ) → ℝ
  /-- transfer rule: `t i θ` is agent `i`'s transfer -/
  t : ι → (ι → ℝ) → ℝ
  q_mem : ∀ θ ∈ E.typeSpace ι, q θ = 0 ∨ q θ = 1

namespace PublicGoodMechanism

variable {E : PublicGoodSetting} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Agent `i`'s ex post utility under truthful reporting: `u_i(θ) = θ_i q(θ) − t_i(θ)`. -/
def u (M : PublicGoodMechanism E ι) (i : ι) (θ : ι → ℝ) : ℝ :=
  θ i * M.q θ - M.t i θ

/-- Dominant strategy incentive compatibility (§4.3.2, "as in the auction example",
Definition 4.1): for all `i`, all `θ ∈ Θ` and all reports `θ_i' ∈ [θ̲, θ̄]`,
`θ_i q(θ_i', θ_{-i}) − t_i(θ_i', θ_{-i}) ≤ θ_i q(θ) − t_i(θ)`. -/
def IsDSIC (M : PublicGoodMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, ∀ x ∈ Set.Icc E.lo E.hi,
    θ i * M.q (Function.update θ i x) - M.t i (Function.update θ i x) ≤
      θ i * M.q θ - M.t i θ

/-- Ex post individual rationality (§4.3.2, Definition 4.2): `θ_i q(θ) − t_i(θ) ≥ 0` for all
`i` and all `θ ∈ Θ`. -/
def IsEPIR (M : PublicGoodMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, 0 ≤ θ i * M.q θ - M.t i θ

/-- Ex post budget balance, written as an equality as in §4.3.2 (p.85):
`∑_i t_i(θ) = c q(θ)` for all `θ ∈ Θ`. -/
def IsBudgetBalanced (M : PublicGoodMechanism E ι) : Prop :=
  ∀ θ ∈ E.typeSpace ι, ∑ i, M.t i θ = E.c * M.q θ

end PublicGoodMechanism

open Classical in
/-- The decision rule of a canonical public good mechanism (Definition 4.4, p.87):
`q(θ) = 1` if `∑_i ψ_i(θ_i) ≥ c`, and `q(θ) = 0` otherwise. -/
noncomputable def canonicalPGQ {ι : Type*} [Fintype ι] (E : PublicGoodSetting)
    (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) : ℝ :=
  if E.c ≤ ∑ i, ψ i (θ i) then 1 else 0

open Classical in
/-- The transfer rule of a canonical public good mechanism (Definition 4.4, p.87):
`t_i(θ) = min {θ̂_i ∈ [θ̲, θ̄] | ψ_i(θ̂_i) + ∑_{j ≠ i} ψ_j(θ_j) ≥ c}` if `q(θ) = 1`, and
`t_i(θ) = 0` if `q(θ) = 0`. The minimum is written as `sInf`; when `q(θ) = 1` the set contains
`θ_i` and, for continuous `ψ_i`, is closed, so the infimum is attained. -/
noncomputable def canonicalPGT {ι : Type*} [Fintype ι] [DecidableEq ι] (E : PublicGoodSetting)
    (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) : ℝ :=
  if canonicalPGQ E ψ θ = 1 then
    sInf {x | x ∈ Set.Icc E.lo E.hi ∧ E.c ≤ ψ i x + ∑ j ∈ Finset.univ.erase i, ψ j (θ j)}
  else 0

/-- Definition 4.4 (p.87), canonical public good mechanism: for every agent `i` there is a
strictly increasing and continuous function `ψ_i : [θ̲, θ̄] → ℝ` such that for all `θ ∈ Θ` the
decision is `canonicalPGQ E ψ θ` and every transfer is `canonicalPGT E ψ i θ`. -/
def PublicGoodMechanism.IsCanonical {E : PublicGoodSetting} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : PublicGoodMechanism E ι) : Prop :=
  ∃ ψ : ι → ℝ → ℝ,
    (∀ i, StrictMonoOn (ψ i) (Set.Icc E.lo E.hi) ∧ ContinuousOn (ψ i) (Set.Icc E.lo E.hi)) ∧
    ∀ θ ∈ E.typeSpace ι,
      M.q θ = canonicalPGQ E ψ θ ∧ ∀ i, M.t i θ = canonicalPGT E ψ i θ

end MechanismDesign.DominantExamples


