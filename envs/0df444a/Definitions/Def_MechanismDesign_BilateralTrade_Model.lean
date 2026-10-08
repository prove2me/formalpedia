-- Prove2me | Definitions.Def_MechanismDesign_BilateralTrade_Model
-- name    : MechanismDesign_BilateralTrade_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T00:38:19.260987+00:00
-- url     : https://prove2.me/theorems/455d0131-a6de-447c-837a-ff98e7f7192e
-- title:
--   Bilateral trade: environment, direct mechanisms, incentive compatibility, individual rationality, budget balance, pivot mechanism
-- statement:
--   A seller $S$ owns a single indivisible good and there is one potential buyer $B$. The seller's value $\theta_S$ is a random variable with distribution function $F_S$ and density $f_S$, where $f_S(\theta_S) > 0$ for all $\theta_S \in [\underline\theta_S, \overline\theta_S]$ and $\int_{\underline\theta_S}^{\overline\theta_S} f_S = 1$; the buyer's value $\theta_B$ has distribution function $F_B$ and density $f_B > 0$ on $[\underline\theta_B, \overline\theta_B]$. Both intervals are nondegenerate, they need not coincide, and $\theta_S$ and $\theta_B$ are independent. Write $\theta = (\theta_S, \theta_B)$, $\Theta = [\underline\theta_S, \overline\theta_S] \times [\underline\theta_B, \overline\theta_B]$, and let $f(\theta) = f_S(\theta_S) f_B(\theta_B)$ be the joint density. The seller's utility is $t$ if she sells and receives $t$, and $\theta_S + t$ if she keeps the good; the buyer's utility is $\theta_B - t$ if he buys and pays $t$, and $-t$ otherwise.
--
--   A **direct mechanism** consists of a trading rule $q : \Theta \to \{0,1\}$ ($q(\theta) = 1$ means trade) and transfer rules $t_S, t_B : \Theta \to \mathbb R$, where $t_S$ is what the seller receives and $t_B$ what the buyer pays. Its interim quantities are
--
--   $$
--   Q_S(\theta_S) = \int q(\theta_S,\theta_B) f_B(\theta_B)\,d\theta_B,\quad T_S(\theta_S) = \int t_S(\theta_S,\theta_B) f_B(\theta_B)\,d\theta_B,\quad U_S(\theta_S) = T_S(\theta_S) + (1 - Q_S(\theta_S))\theta_S,
--   $$
--
--   $$
--   Q_B(\theta_B) = \int q(\theta_S,\theta_B) f_S(\theta_S)\,d\theta_S,\quad T_B(\theta_B) = \int t_B(\theta_S,\theta_B) f_S(\theta_S)\,d\theta_S,\quad U_B(\theta_B) = Q_B(\theta_B)\theta_B - T_B(\theta_B).
--   $$
--
--   The mechanism is **incentive-compatible** if no seller type $\theta_S$ gains by reporting another type $\theta_S'$, i.e. $T_S(\theta_S') + (1-Q_S(\theta_S'))\theta_S \le U_S(\theta_S)$, and likewise $Q_B(\theta_B')\theta_B - T_B(\theta_B') \le U_B(\theta_B)$ for the buyer. It is **individually rational** if $U_S(\theta_S) \ge \theta_S$ and $U_B(\theta_B) \ge 0$ for all types. It is **ex post budget balanced** if $t_S(\theta) = t_B(\theta)$ for all $\theta \in \Theta$, and **ex ante budget balanced** if $\mathbb E[t_S(\theta)] = \mathbb E[t_B(\theta)]$. The ex ante expected difference of transfers (the designer's expected profit) is $\mathbb E[t_B(\theta) - t_S(\theta)]$, and expected welfare is the expectation of
--
--   $$
--   q(\theta)\theta_B - t_B + (1-q(\theta))\theta_S + t_S = \theta_S + q(\theta)(\theta_B - \theta_S) + t_S - t_B.
--   $$
--
--   A **first-best trading rule** $q^*$ takes values in $\{0,1\}$, trades when $\theta_B > \theta_S$ and does not trade when $\theta_B < \theta_S$; the decision when $\theta_B = \theta_S$ is arbitrary. The **pivot mechanism** for $q^*$ uses $q^*$ and the transfers
--
--   $$
--   t_S(\theta) = q^*(\overline\theta_S, \theta_B)\overline\theta_S + \big(q^*(\theta) - q^*(\overline\theta_S,\theta_B)\big)\theta_B, \qquad t_B(\theta) = q^*(\theta_S, \underline\theta_B)\underline\theta_B + \big(q^*(\theta) - q^*(\theta_S,\underline\theta_B)\big)\theta_S.
--   $$
--
--   The seller's virtual cost is $\psi_S(\theta_S) = \theta_S + F_S(\theta_S)/f_S(\theta_S)$ and the buyer's virtual valuation is $\psi_B(\theta_B) = \theta_B - (1 - F_B(\theta_B))/f_B(\theta_B)$; the distributions are **regular** if both are (weakly) increasing. For $\lambda > 0$ the second-best rule trades iff
--
--   $$
--   \theta_B - \frac{\lambda}{1+\lambda}\,\frac{1 - F_B(\theta_B)}{f_B(\theta_B)} \;\ge\; \theta_S + \frac{\lambda}{1+\lambda}\,\frac{F_S(\theta_S)}{f_S(\theta_S)},
--   $$
--
--   and the profit-maximizing rule trades iff $\psi_B(\theta_B) > \psi_S(\theta_S)$. Example 3.4 is the environment in which both values are uniform on $[0,1]$.
--
--   These are the objects of every statement about bilateral trade in Section 3.4.
--
--   **Formalization Note** A type vector is a pair `θ : ℝ × ℝ` with `θ.1 = θ_S` and `θ.2 = θ_B`. The prior is Lebesgue measure on $\Theta$ with density $f_S(\theta_S) f_B(\theta_B)$. The trading and transfer rules are total functions on `ℝ × ℝ`, of which only the values on $\Theta$ matter; `q` is real-valued with `q θ ∈ {0,1}` on $\Theta$. The book omits measurability requirements (Ch. 2 note 2); `WellDefined` supplies them: `q`, `t_S`, `t_B` measurable, `t_S`, `t_B` integrable under the prior, and the sections defining $T_S$, $T_B$ integrable. `Admissible` means well defined, incentive-compatible and individually rational. "Increasing" in the regularity assumption is weak monotonicity on the support, the book's convention.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.63–66, §3.4.1–3.4.3, Definition 3.9, Eqs. (3.60)–(3.61), Definition 3.10; p.70, Assumption 3.3, Eq. (3.70); p.72, Proposition 3.14 (i); p.73, Example 3.4

import Mathlib

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- The bilateral trade environment of Börgers §3.4.1 (p.63). A seller `S` owns one indivisible
good and a buyer `B` may buy it. The seller's value `θ_S` has density `fS`, strictly positive on
`[loS, hiS]` and integrating to `1` there; the buyer's value `θ_B` has density `fB`, strictly
positive on `[loB, hiB]` and integrating to `1` there. The two supports are separate intervals and
the two values are independent. A type vector is `θ = (θ_S, θ_B) : ℝ × ℝ` (first coordinate the
seller's, second the buyer's). -/
structure Environment where
  /-- the lower end `θ̲_S` of the seller's support -/
  loS : ℝ
  /-- the upper end `θ̄_S` of the seller's support -/
  hiS : ℝ
  /-- the lower end `θ̲_B` of the buyer's support -/
  loB : ℝ
  /-- the upper end `θ̄_B` of the buyer's support -/
  hiB : ℝ
  /-- the density `f_S` of the seller's value -/
  fS : ℝ → ℝ
  /-- the density `f_B` of the buyer's value -/
  fB : ℝ → ℝ
  loS_lt_hiS : loS < hiS
  loB_lt_hiB : loB < hiB
  fS_measurable : Measurable fS
  fB_measurable : Measurable fB
  fS_pos : ∀ x ∈ Set.Icc loS hiS, 0 < fS x
  fB_pos : ∀ y ∈ Set.Icc loB hiB, 0 < fB y
  fS_intervalIntegrable : IntervalIntegrable fS volume loS hiS
  fB_intervalIntegrable : IntervalIntegrable fB volume loB hiB
  fS_integral : ∫ x in loS..hiS, fS x = 1
  fB_integral : ∫ y in loB..hiB, fB y = 1

variable (E : Environment)

/-- The type space `Θ = [θ̲_S, θ̄_S] × [θ̲_B, θ̄_B]`. -/
def Environment.typeSpace : Set (ℝ × ℝ) :=
  Set.Icc E.loS E.hiS ×ˢ Set.Icc E.loB E.hiB

/-- The joint distribution `F` of `θ = (θ_S, θ_B)`: density `f(θ) = f_S(θ_S) f_B(θ_B)` on `Θ`
(independence), no mass outside `Θ`. -/
noncomputable def Environment.prior : Measure (ℝ × ℝ) :=
  (volume.restrict E.typeSpace).withDensity (fun θ => ENNReal.ofReal (E.fS θ.1 * E.fB θ.2))

/-- The seller's distribution function `F_S(x) = ∫_{θ̲_S}^{x} f_S`. -/
noncomputable def Environment.cdfS (x : ℝ) : ℝ := ∫ z in E.loS..x, E.fS z

/-- The buyer's distribution function `F_B(y) = ∫_{θ̲_B}^{y} f_B`. -/
noncomputable def Environment.cdfB (y : ℝ) : ℝ := ∫ z in E.loB..y, E.fB z

/-- The seller's virtual cost `ψ_S(θ_S) = θ_S + F_S(θ_S) / f_S(θ_S)` (Assumption 3.3, p.70). -/
noncomputable def Environment.psiS (x : ℝ) : ℝ := x + E.cdfS x / E.fS x

/-- The buyer's virtual valuation `ψ_B(θ_B) = θ_B − (1 − F_B(θ_B)) / f_B(θ_B)`
(Assumption 3.3, p.70). -/
noncomputable def Environment.psiB (y : ℝ) : ℝ := y - (1 - E.cdfB y) / E.fB y

/-- Assumption 3.3 (p.70): `F_S` and `F_B` are regular, i.e. `ψ_S` and `ψ_B` are (weakly)
increasing on the respective supports ("increasing" means weakly increasing throughout the book,
Ch. 2 note 3, p.235). -/
def Environment.Regular : Prop :=
  MonotoneOn E.psiS (Set.Icc E.loS E.hiS) ∧ MonotoneOn E.psiB (Set.Icc E.loB E.hiB)

/-- A direct mechanism, Definition 3.9 (pp.63–64): a deterministic trading rule `q : Θ → {0, 1}`
(`q θ = 1` means trade) and transfer rules `tS` (what the seller **receives**) and `tB` (what the
buyer **pays**). The functions are total on `ℝ × ℝ`; only their values on `Θ` matter. -/
structure DirectMechanism where
  /-- the trading rule `q` -/
  q : ℝ × ℝ → ℝ
  /-- the seller's receipt `t_S` -/
  tS : ℝ × ℝ → ℝ
  /-- the buyer's payment `t_B` -/
  tB : ℝ × ℝ → ℝ
  q_mem : ∀ θ ∈ E.typeSpace, q θ = 0 ∨ q θ = 1

variable {E}

/-- The measurability and integrability the book leaves implicit (Ch. 2 note 2, p.235):
`q`, `t_S`, `t_B` are measurable, `t_S` and `t_B` are integrable under the prior, and so are the
sections that define the interim transfers `T_S`, `T_B`. -/
structure DirectMechanism.WellDefined (m : DirectMechanism E) : Prop where
  q_measurable : Measurable m.q
  tS_measurable : Measurable m.tS
  tB_measurable : Measurable m.tB
  tS_integrable : Integrable m.tS E.prior
  tB_integrable : Integrable m.tB E.prior
  tS_section : ∀ x ∈ Set.Icc E.loS E.hiS,
    IntervalIntegrable (fun y => m.tS (x, y) * E.fB y) volume E.loB E.hiB
  tB_section : ∀ y ∈ Set.Icc E.loB E.hiB,
    IntervalIntegrable (fun x => m.tB (x, y) * E.fS x) volume E.loS E.hiS

/-- `Q_S(θ_S)`: the probability of trade conditional on the seller's type (p.64). -/
noncomputable def DirectMechanism.QS (m : DirectMechanism E) (x : ℝ) : ℝ :=
  ∫ y in E.loB..E.hiB, m.q (x, y) * E.fB y

/-- `Q_B(θ_B)`: the probability of trade conditional on the buyer's type (p.64). -/
noncomputable def DirectMechanism.QB (m : DirectMechanism E) (y : ℝ) : ℝ :=
  ∫ x in E.loS..E.hiS, m.q (x, y) * E.fS x

/-- `T_S(θ_S)`: the seller's expected receipt conditional on her type (p.64). -/
noncomputable def DirectMechanism.TS (m : DirectMechanism E) (x : ℝ) : ℝ :=
  ∫ y in E.loB..E.hiB, m.tS (x, y) * E.fB y

/-- `T_B(θ_B)`: the buyer's expected payment conditional on his type (p.64). -/
noncomputable def DirectMechanism.TB (m : DirectMechanism E) (y : ℝ) : ℝ :=
  ∫ x in E.loS..E.hiS, m.tB (x, y) * E.fS x

/-- `U_S(θ_S) = T_S(θ_S) + (1 − Q_S(θ_S)) θ_S` (p.64). -/
noncomputable def DirectMechanism.US (m : DirectMechanism E) (x : ℝ) : ℝ :=
  m.TS x + (1 - m.QS x) * x

/-- `U_B(θ_B) = Q_B(θ_B) θ_B − T_B(θ_B)` (p.64). -/
noncomputable def DirectMechanism.UB (m : DirectMechanism E) (y : ℝ) : ℝ :=
  m.QB y * y - m.TB y

/-- Bayesian incentive compatibility (p.64, "defined as before", Definition 3.2): no seller type
gains by reporting another seller type, and no buyer type by reporting another buyer type,
given truthful reporting by the other agent. -/
def DirectMechanism.IsIC (m : DirectMechanism E) : Prop :=
  (∀ x ∈ Set.Icc E.loS E.hiS, ∀ x' ∈ Set.Icc E.loS E.hiS,
      m.TS x' + (1 - m.QS x') * x ≤ m.TS x + (1 - m.QS x) * x) ∧
  (∀ y ∈ Set.Icc E.loB E.hiB, ∀ y' ∈ Set.Icc E.loB E.hiB,
      m.QB y' * y - m.TB y' ≤ m.QB y * y - m.TB y)

/-- Interim individual rationality (p.64): `U_S(θ_S) ≥ θ_S` (the seller's value of keeping the
good) and `U_B(θ_B) ≥ 0` for all types. -/
def DirectMechanism.IsIR (m : DirectMechanism E) : Prop :=
  (∀ x ∈ Set.Icc E.loS E.hiS, x ≤ m.US x) ∧ (∀ y ∈ Set.Icc E.loB E.hiB, 0 ≤ m.UB y)

/-- Well-defined, incentive-compatible and individually rational. -/
def DirectMechanism.Admissible (m : DirectMechanism E) : Prop :=
  m.WellDefined ∧ m.IsIC ∧ m.IsIR

/-- Ex post budget balance (p.65): `t_S(θ) = t_B(θ)` for every `θ ∈ Θ` (an equality). -/
def DirectMechanism.ExPostBB (m : DirectMechanism E) : Prop :=
  ∀ θ ∈ E.typeSpace, m.tS θ = m.tB θ

/-- Ex ante budget balance (p.65): the seller's ex ante expected receipt equals the buyer's ex
ante expected payment. -/
def DirectMechanism.ExAnteBB (m : DirectMechanism E) : Prop :=
  ∫ θ, m.tS θ ∂E.prior = ∫ θ, m.tB θ ∂E.prior

/-- The ex ante expected difference `E[t_B(θ) − t_S(θ)]` between the buyer's and the seller's
transfers (Lemmas 3.10–3.11); it is also the designer's expected profit of §3.4.4 (p.72). -/
noncomputable def DirectMechanism.expectedSurplus (m : DirectMechanism E) : ℝ :=
  ∫ θ, (m.tB θ - m.tS θ) ∂E.prior

/-- Expected welfare, the expectation of Eq. (3.60):
`q(θ) θ_B − t_B + (1 − q(θ)) θ_S + t_S = θ_S + q(θ)(θ_B − θ_S) + t_S − t_B`. -/
noncomputable def DirectMechanism.welfare (m : DirectMechanism E) : ℝ :=
  ∫ θ, (θ.1 + m.q θ * (θ.2 - θ.1) + m.tS θ - m.tB θ) ∂E.prior

variable (E)

/-- A first-best trading rule, Eq. (3.61) (pp.65–66): `q(θ) ∈ {0, 1}` on `Θ`, trade when
`θ_B > θ_S`, no trade when `θ_B < θ_S`; "the decision in the case of equality of values is
arbitrary", so it is left free. -/
def IsFirstBestRule (q : ℝ × ℝ → ℝ) : Prop :=
  ∀ θ ∈ E.typeSpace, (q θ = 0 ∨ q θ = 1) ∧ (θ.1 < θ.2 → q θ = 1) ∧ (θ.2 < θ.1 → q θ = 0)

/-- The pivot mechanism, Definition 3.10 (p.66), for a first-best trading rule `q*`:
`t_S(θ) = q*(θ̄_S, θ_B) θ̄_S + (q*(θ) − q*(θ̄_S, θ_B)) θ_B` and
`t_B(θ) = q*(θ_S, θ̲_B) θ̲_B + (q*(θ) − q*(θ_S, θ̲_B)) θ_S`. -/
def pivot (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q) : DirectMechanism E where
  q := q
  tS := fun θ => q (E.hiS, θ.2) * E.hiS + (q θ - q (E.hiS, θ.2)) * θ.2
  tB := fun θ => q (θ.1, E.loB) * E.loB + (q θ - q (θ.1, E.loB)) * θ.1
  q_mem := fun θ hθ => (hq θ hθ).1

/-- The second-best trading rule with multiplier `λ` (written `lam`), Eq. (3.70) and
Proposition 3.13 (i) (p.71): trade iff
`θ_B − (λ/(1+λ)) (1 − F_B(θ_B))/f_B(θ_B) ≥ θ_S + (λ/(1+λ)) F_S(θ_S)/f_S(θ_S)`. -/
noncomputable def lambdaRule (lam : ℝ) (θ : ℝ × ℝ) : ℝ :=
  if θ.1 + lam / (1 + lam) * (E.cdfS θ.1 / E.fS θ.1)
      ≤ θ.2 - lam / (1 + lam) * ((1 - E.cdfB θ.2) / E.fB θ.2) then 1 else 0

/-- The profit-maximizing trading rule, Proposition 3.14 (i) (p.72): trade iff
`θ_B − (1 − F_B(θ_B))/f_B(θ_B) > θ_S + F_S(θ_S)/f_S(θ_S)`, i.e. `ψ_B(θ_B) > ψ_S(θ_S)`. -/
noncomputable def profitRule (θ : ℝ × ℝ) : ℝ :=
  if E.psiS θ.1 < E.psiB θ.2 then 1 else 0

/-- Example 3.4 (p.73): both values uniformly distributed on `[0, 1]`. -/
noncomputable def uniformEnv : Environment where
  loS := 0
  hiS := 1
  loB := 0
  hiB := 1
  fS := fun _ => 1
  fB := fun _ => 1
  loS_lt_hiS := zero_lt_one
  loB_lt_hiB := zero_lt_one
  fS_measurable := measurable_const
  fB_measurable := measurable_const
  fS_pos := fun _ _ => zero_lt_one
  fB_pos := fun _ _ => zero_lt_one
  fS_intervalIntegrable := intervalIntegrable_const
  fB_intervalIntegrable := intervalIntegrable_const
  fS_integral := by simp
  fB_integral := by simp

end MechanismDesign.BilateralTrade


