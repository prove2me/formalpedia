-- Prove2me | Definitions.Def_MechanismDesign_PublicGoods_Model
-- name    : MechanismDesign_PublicGoods_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T00:03:14.079886+00:00
-- url     : https://prove2.me/theorems/63bf272c-3fe4-44e9-a592-7ffcd8593ef5
-- title:
--   Public goods (Börgers §3.3): types, direct mechanisms, IC, IR, budget balance, first best, pivot, second best
-- statement:
--   This file sets up the independent-private-values public goods model of Börgers, §3.3.
--
--   **Environment.** There are $N \ge 2$ agents $I = \{1,\dots,N\}$. They decide whether to produce an indivisible, nonexcludable public good, $g \in \{0,1\}$, at cost $c > 0$. Agent $i$'s utility from decision $g$ and transfer $t_i$ is $\theta_i g - t_i$. The type $\theta_i$ has a density $f_i$ that is strictly positive on the support $[\underline\theta, \bar\theta]$, where $0 \le \underline\theta < \bar\theta$, and integrates to $1$ over it; the types are independent. We write $\Theta = [\underline\theta,\bar\theta]^N$, $F_i(x) = \int_{\underline\theta}^{x} f_i$, and $f(\theta) = \prod_i f_i(\theta_i)$ for the joint density of $\theta = (\theta_1,\dots,\theta_N)$. The **virtual valuation** is
--   $$\psi_i(\theta_i) = \theta_i - \frac{1 - F_i(\theta_i)}{f_i(\theta_i)},$$
--   and $F_i$ is **regular** (Assumption 3.2) if $\psi_i$ is strictly increasing on $[\underline\theta,\bar\theta]$.
--
--   **Direct mechanisms** (Definition 3.4). A direct mechanism is a decision rule $q : \Theta \to \{0,1\}$ together with transfer rules $t_i : \Theta \to \mathbb R$. Given a direct mechanism, $Q_i(\theta_i)$ and $T_i(\theta_i)$ are the probability of production and the expected transfer of agent $i$ when she reports $\theta_i$ and the other agents' types are drawn from their distribution, and $U_i(\theta_i) = Q_i(\theta_i)\theta_i - T_i(\theta_i)$.
--
--   1. **Incentive compatibility** (Definition 3.2): $\theta_i Q_i(\theta_i) - T_i(\theta_i) \ge \theta_i Q_i(\theta_i') - T_i(\theta_i')$ for all $i$ and all $\theta_i, \theta_i' \in [\underline\theta,\bar\theta]$.
--   2. **Individual rationality** (Definition 3.3): $U_i(\theta_i) \ge 0$ for all $i$ and $\theta_i$.
--   3. **Ex post budget balance** (Definition 3.5): $\sum_{i} t_i(\theta) \ge c\,q(\theta)$ for every $\theta \in \Theta$.
--   4. **Ex ante budget balance** (Definition 3.6): $\int_\Theta \sum_i t_i(\theta) f(\theta)\,d\theta \ge \int_\Theta c\,q(\theta) f(\theta)\,d\theta$.
--   5. **Equivalence** (Definition 3.7): two direct mechanisms are equivalent if they have the same decision rule on $\Theta$ and, for every agent $i$ and every report $\theta_i'$, the same expected transfer of agent $i$ given that she reports $\theta_i'$.
--   6. **First best** ((3.21)–(3.22)): the decision rule is $q^*(\theta) = 1$ if $\sum_i \theta_i \ge c$ and $0$ otherwise, and $\sum_i t_i(\theta) = c\,q^*(\theta)$ for every $\theta \in \Theta$.
--   7. **Pivot mechanism** (Definition 3.8): decision rule $q^*$ and transfers
--   $$t_i(\theta) = \underline\theta\, q^*(\underline\theta,\theta_{-i}) + \big(q^*(\theta) - q^*(\underline\theta,\theta_{-i})\big)\Big(c - \sum_{j \ne i}\theta_j\Big).$$
--   8. The **expected budget surplus** (which is also the designer's expected profit) is $\int_\Theta \big(\sum_i t_i(\theta) - c\,q(\theta)\big) f(\theta)\,d\theta$, and **expected welfare** is the expectation of (3.17), $\int_\Theta \big((\sum_i\theta_i) q(\theta) - \sum_i t_i(\theta)\big) f(\theta)\,d\theta$.
--   9. A mechanism is **second best** (p.54) if it is incentive compatible, individually rational and ex ante budget balanced and maximizes expected welfare among all such direct mechanisms; it **maximizes expected profit** (§3.3.5) if it is incentive compatible and individually rational and maximizes the expected budget surplus among all such mechanisms.
--   10. The **second best rule** for a multiplier $\lambda$ produces iff $\sum_i \theta_i > c + \sum_i \frac{\lambda}{1+\lambda}\frac{1-F_i(\theta_i)}{f_i(\theta_i)}$; the **profit rule** produces iff $\sum_i \theta_i > c + \sum_i \frac{1-F_i(\theta_i)}{f_i(\theta_i)}$.
--   11. **Example 3.3**: $N = 2$, both types uniform on $[0,1]$, cost $c$; the threshold rule with threshold $s$ produces iff $\theta_1 + \theta_2 > s$.
--
--   These are the objects every result of §3.3 is stated in terms of.
--
--   **Formalization Note** Agents are `Fin N`. Types are vectors `Fin N → ℝ`; the joint distribution is the product measure of the marginals $f_i(x)\,dx$ on $[\underline\theta,\bar\theta]$, which encodes independence. $Q_i(x)$ and $T_i(x)$ are computed by integrating $q$ and $t_i$ against the joint distribution after overwriting coordinate $i$ by $x$; since every marginal is a probability measure this is the integral over $\theta_{-i}$ against $f_{-i}$. Because types are independent, the expected transfer given true type $\theta_i$ and report $\theta_i'$ does not depend on $\theta_i$, so Definition 3.7 compares $T_i(\theta_i')$. The book omits measurability (note 2 to Ch. 2) and the existence of conditional expectations (note 1 to Ch. 3); the predicate `IsDirect` makes them explicit: $q$ and each $t_i$ are Borel measurable, each $t_i$ is integrable, and each conditional expectation of $t_i$ given one agent's type exists. The decision rule is real-valued with values in $\{0,1\}$ on $\Theta$; its values outside $\Theta$ play no role.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.45–58, §3.3.1–3.3.6: setup p.46 and (3.17); Definition 3.4 p.47; Definitions 3.2–3.3 p.36; Definitions 3.5 p.47, 3.6–3.7 p.48; (3.21)–(3.22) p.50; Definition 3.8 p.51; second best p.54; (3.34) and Assumption 3.2 p.56; §3.3.5 p.57; Example 3.3 p.58

import Mathlib

namespace MechanismDesign.PublicGoods

open MeasureTheory

/-- The public-goods environment of Börgers, *An Introduction to the Theory of Mechanism Design*,
§3.3.1 (pp.45–46). There are `N ≥ 2` agents `Fin N`. Agent `i`'s type `θ_i` has density `f i`,
strictly positive on the common support `[θlo, θhi]` with `0 ≤ θlo < θhi`, and integrating to `1`
over it. The cost of the public good is `c > 0`. -/
structure Setting (N : ℕ) where
  /-- lower end `θ̲` of the type interval -/
  θlo : ℝ
  /-- upper end `θ̄` of the type interval -/
  θhi : ℝ
  /-- density `f_i` of agent `i`'s type -/
  f : Fin N → ℝ → ℝ
  /-- cost `c` of producing the public good -/
  c : ℝ
  two_le : 2 ≤ N
  θlo_nonneg : 0 ≤ θlo
  θlo_lt_θhi : θlo < θhi
  f_pos : ∀ i, ∀ x ∈ Set.Icc θlo θhi, 0 < f i x
  f_intervalIntegrable : ∀ i, IntervalIntegrable (f i) volume θlo θhi
  f_integral : ∀ i, ∫ x in θlo..θhi, f i x = 1
  c_pos : 0 < c

namespace Setting

variable {N : ℕ} (S : Setting N)

/-- The type space `Θ = [θ̲, θ̄]^N`. -/
def typeSpace : Set (Fin N → ℝ) :=
  Set.univ.pi fun _ => Set.Icc S.θlo S.θhi

/-- The distribution of agent `i`'s type: Lebesgue measure on `[θ̲, θ̄]` with density `f_i`. -/
noncomputable def marginal (i : Fin N) : Measure ℝ :=
  (volume.restrict (Set.Icc S.θlo S.θhi)).withDensity fun x => ENNReal.ofReal (S.f i x)

/-- The joint distribution of the type vector `θ`: the product of the marginals (types are
independent), i.e. the measure `f(θ) dθ` on `Θ` with `f(θ) = ∏_i f_i(θ_i)`. -/
noncomputable def μ : Measure (Fin N → ℝ) :=
  Measure.pi S.marginal

/-- The cumulative distribution function `F_i(x) = ∫_{θ̲}^{x} f_i`. -/
noncomputable def cdf (i : Fin N) (x : ℝ) : ℝ :=
  ∫ y in S.θlo..x, S.f i y

/-- The virtual valuation `ψ_i(x) = x − (1 − F_i(x)) / f_i(x)` (Assumption 3.2, p.56). -/
noncomputable def virtualValuation (i : Fin N) (x : ℝ) : ℝ :=
  x - (1 - S.cdf i x) / S.f i x

/-- Assumption 3.2 (p.56): `F_i` is regular, i.e. `ψ_i` is strictly increasing on `[θ̲, θ̄]`. -/
def IsRegular (i : Fin N) : Prop :=
  StrictMonoOn (S.virtualValuation i) (Set.Icc S.θlo S.θhi)

/-- The first best decision rule (3.21), p.50: produce iff `∑_i θ_i ≥ c` (ties produce, note 2
to Ch. 3, p.235). -/
noncomputable def qStar (θ : Fin N → ℝ) : ℝ :=
  if S.c ≤ ∑ i, θ i then 1 else 0

end Setting

/-- The data of a direct mechanism (Definition 3.4, p.47): a decision rule `q` and, for each
agent `i`, a transfer rule `t i`. Whether the data form a direct mechanism in the book's sense is
the predicate `DirectMechanism.IsDirect`. -/
structure DirectMechanism (N : ℕ) where
  /-- the decision rule `q(θ)` (whether the public good is produced) -/
  q : (Fin N → ℝ) → ℝ
  /-- the transfer `t_i(θ)` that agent `i` pays to the community -/
  t : Fin N → (Fin N → ℝ) → ℝ

namespace DirectMechanism

variable {N : ℕ} (S : Setting N) (M : DirectMechanism N)

/-- `M` is a direct mechanism in the sense of Definition 3.4 (p.47): the decision rule takes
values in `{0, 1}` on `Θ`. The book omits measurability (note 2 to Ch. 2, p.235) and the
existence of conditional expectations (note 1 to Ch. 3); they are made explicit here: `q` and
every `t_i` are measurable, every `t_i` is integrable, and every conditional expectation of `t_i`
given one agent's type `θ_j = x ∈ [θ̲, θ̄]` exists. -/
def IsDirect : Prop :=
  (∀ θ ∈ S.typeSpace, M.q θ = 0 ∨ M.q θ = 1) ∧ Measurable M.q ∧
    ∀ i, Measurable (M.t i) ∧ Integrable (M.t i) S.μ ∧
      ∀ j, ∀ x ∈ Set.Icc S.θlo S.θhi, Integrable (fun θ => M.t i (Function.update θ j x)) S.μ

/-- The interim probability `Q_i(x)` that the good is produced when agent `i` reports `x` and the
others' types are drawn from their distribution. Integrating over the whole vector `θ` with the
`i`-th coordinate overwritten equals integrating over `θ_{-i}` with density `f_{-i}`. -/
noncomputable def interimQ (i : Fin N) (x : ℝ) : ℝ :=
  ∫ θ, M.q (Function.update θ i x) ∂S.μ

/-- The interim expected transfer `T_i(x)` of agent `i` when she reports `x`. -/
noncomputable def interimT (i : Fin N) (x : ℝ) : ℝ :=
  ∫ θ, M.t i (Function.update θ i x) ∂S.μ

/-- The interim expected utility `U_i(x) = Q_i(x) x − T_i(x)`. -/
noncomputable def interimU (i : Fin N) (x : ℝ) : ℝ :=
  M.interimQ S i x * x - M.interimT S i x

/-- Incentive compatibility (Definition 3.2, p.36, used in §3.3 by p.47):
`θ_i Q_i(θ_i) − T_i(θ_i) ≥ θ_i Q_i(θ_i') − T_i(θ_i')` for all `i` and `θ_i, θ_i' ∈ [θ̲, θ̄]`. -/
def IsIC : Prop :=
  ∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, ∀ x' ∈ Set.Icc S.θlo S.θhi,
    x * M.interimQ S i x' - M.interimT S i x' ≤ x * M.interimQ S i x - M.interimT S i x

/-- Individual rationality (Definition 3.3, p.36): `U_i(θ_i) ≥ 0` for all `i`, `θ_i`. -/
def IsIR : Prop :=
  ∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, 0 ≤ M.interimU S i x

/-- Definition 3.5 (p.47), ex post budget balance: `∑_i t_i(θ) ≥ c q(θ)` for every `θ ∈ Θ`. -/
def IsExPostBB : Prop :=
  ∀ θ ∈ S.typeSpace, S.c * M.q θ ≤ ∑ i, M.t i θ

/-- Definition 3.6 (p.48), ex ante budget balance:
`∫_Θ ∑_i t_i(θ) f(θ) dθ ≥ ∫_Θ c q(θ) f(θ) dθ`. -/
def IsExAnteBB : Prop :=
  ∫ θ, S.c * M.q θ ∂S.μ ≤ ∫ θ, ∑ i, M.t i θ ∂S.μ

/-- Definition 3.7 (p.48): `M` and `M'` are equivalent if they have the same decision rule on `Θ`
and, for every agent `i` and every report `θ_i'`, the same expected transfer of agent `i` given
that she reports `θ_i'`. (Types are independent, so this conditional expectation is the same for
every true type `θ_i` of agent `i`; it is `T_i(θ_i')`.) -/
def Equivalent (M' : DirectMechanism N) : Prop :=
  (∀ θ ∈ S.typeSpace, M.q θ = M'.q θ) ∧
    ∀ i, ∀ x ∈ Set.Icc S.θlo S.θhi, M.interimT S i x = M'.interimT S i x

/-- A first best mechanism ((3.21)–(3.22), p.50): the decision rule is `q*` and the transfers add
up to exactly `c` when `q*(θ) = 1` and to `0` otherwise, for every `θ ∈ Θ`. -/
def IsFirstBest : Prop :=
  ∀ θ ∈ S.typeSpace, M.q θ = S.qStar θ ∧ ∑ i, M.t i θ = S.c * S.qStar θ

/-- The ex ante expected budget surplus, revenue minus cost: `∫_Θ (∑_i t_i(θ) − c q(θ)) f(θ) dθ`.
This is also the designer's expected profit in §3.3.5. -/
noncomputable def budgetSurplus : ℝ :=
  ∫ θ, (∑ i, M.t i θ - S.c * M.q θ) ∂S.μ

/-- Expected utilitarian welfare, the expectation of (3.17), p.46:
`∫_Θ ((∑_i θ_i) q(θ) − ∑_i t_i(θ)) f(θ) dθ`. -/
noncomputable def welfare : ℝ :=
  ∫ θ, ((∑ i, θ i) * M.q θ - ∑ i, M.t i θ) ∂S.μ

/-- Second best (p.54): `M` is incentive compatible, individually rational and ex ante budget
balanced, and maximizes expected welfare among all such direct mechanisms. -/
def IsSecondBest : Prop :=
  M.IsDirect S ∧ M.IsIC S ∧ M.IsIR S ∧ M.IsExAnteBB S ∧
    ∀ M' : DirectMechanism N, M'.IsDirect S → M'.IsIC S → M'.IsIR S → M'.IsExAnteBB S →
      M'.welfare S ≤ M.welfare S

/-- Profit maximization (§3.3.5, p.57): `M` is incentive compatible and individually rational
and maximizes expected profit (revenue minus cost) among all such direct mechanisms. -/
def IsProfitMax : Prop :=
  M.IsDirect S ∧ M.IsIC S ∧ M.IsIR S ∧
    ∀ M' : DirectMechanism N, M'.IsDirect S → M'.IsIC S → M'.IsIR S →
      M'.budgetSurplus S ≤ M.budgetSurplus S

end DirectMechanism

namespace Setting

variable {N : ℕ} (S : Setting N)

/-- The pivot mechanism (Definition 3.8, p.51): decision rule `q*` and transfers
`t_i(θ) = θ̲ q*(θ̲, θ_{-i}) + (q*(θ) − q*(θ̲, θ_{-i})) (c − ∑_{j ≠ i} θ_j)`. -/
noncomputable def pivot : DirectMechanism N where
  q := S.qStar
  t := fun i θ =>
    S.θlo * S.qStar (Function.update θ i S.θlo) +
      (S.qStar θ - S.qStar (Function.update θ i S.θlo)) *
        (S.c - ∑ j ∈ Finset.univ.erase i, θ j)

/-- The second best decision rule (3.34) / Proposition 3.8 (i), p.56, for multiplier `λ`:
produce iff `∑_i θ_i > c + ∑_i (λ / (1 + λ)) (1 − F_i(θ_i)) / f_i(θ_i)`. -/
noncomputable def secondBestRule (lam : ℝ) (θ : Fin N → ℝ) : ℝ :=
  if S.c + ∑ i, lam / (1 + lam) * ((1 - S.cdf i (θ i)) / S.f i (θ i)) < ∑ i, θ i then 1 else 0

/-- The profit-maximizing decision rule of Proposition 3.9 (i), p.57:
produce iff `∑_i θ_i > c + ∑_i (1 − F_i(θ_i)) / f_i(θ_i)`. -/
noncomputable def profitRule (θ : Fin N → ℝ) : ℝ :=
  if S.c + ∑ i, (1 - S.cdf i (θ i)) / S.f i (θ i) < ∑ i, θ i then 1 else 0

end Setting

/-- Example 3.3 (p.58): `N = 2`, both types uniformly distributed on `[0, 1]` (density `1`), and
cost `c` (the example assumes `0 < c < 2`; the setting itself needs only `c > 0`). -/
noncomputable def uniformExample (c : ℝ) (hc : 0 < c) : Setting 2 where
  θlo := 0
  θhi := 1
  f := fun _ _ => 1
  c := c
  two_le := le_refl 2
  θlo_nonneg := le_refl 0
  θlo_lt_θhi := zero_lt_one
  f_pos := fun _ _ _ => one_pos
  f_intervalIntegrable := fun _ => intervalIntegrable_const
  f_integral := fun _ => by simp
  c_pos := hc

/-- The threshold decision rule of Example 3.3: produce iff `θ_1 + θ_2 > s`. -/
noncomputable def thresholdRule (s : ℝ) (θ : Fin 2 → ℝ) : ℝ :=
  if s < θ 0 + θ 1 then 1 else 0

end MechanismDesign.PublicGoods


