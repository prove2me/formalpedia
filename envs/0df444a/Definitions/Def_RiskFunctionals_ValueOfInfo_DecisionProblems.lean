-- Prove2me | Definitions.Def_RiskFunctionals_ValueOfInfo_DecisionProblems
-- name    : RiskFunctionals_ValueOfInfo_DecisionProblems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:41.669359+00:00
-- url     : https://prove2.me/theorems/951041e3-2777-471f-ba29-7ce087e53b40
-- title:
--   The multi-stage decision problem on a tree: non-anticipative and clairvoyant decisions, conditional acceptability values (Eqs. (5.13)–(5.17))
-- statement:
--   Let $(\nu_t)_{t=0,\dots,T}$ be a stochastic process on $(\Omega,\mathcal F,P)$, $\nu_t$ taking values in $\mathcal N_t$, with $\nu_0$ the root of the tree. Put $\mathcal F_t=\sigma(\nu_t)$, the **standard filtration** $\boldsymbol{\mathcal F}=(\mathcal F_0,\dots,\mathcal F_T)$ and the **clairvoyant's filtration** $\boldsymbol{\mathcal F}^T=(\mathcal F_T,\dots,\mathcal F_T)$. The **scenario variables** are $\xi_t=f_t(\nu_t)$, $t=1,\dots,T$, with values in a space $\Xi$, and $H(x_0,\xi_1,x_1,\dots,x_{T-1},\xi_T)$, written $H(x,\xi)$, is a real **profit function** of the decision sequence $x=(x_0,\dots,x_{T-1})$, which must lie in a **decision space** $\mathcal X$. A decision sequence is a random variable $x(\omega)=(x_0(\omega),\dots,x_{T-1}(\omega))$.
--
--   1. $x$ is **non-anticipative**, $x\lhd\boldsymbol{\mathcal F}$, if $x_t$ is $\mathcal F_t$-measurable for $t=0,\dots,T-1$.
--   2. $x$ is **clairvoyant**, $x\lhd\boldsymbol{\mathcal F}^T$, if every $x_t$ is $\mathcal F_T$-measurable.
--   3. For a single-period, version-independent acceptability functional $\mathcal A$ (a real map on distributions on $\mathbb R$), a stage $t$, a node $v$ of $\nu_t$ and a random variable $Y$, $\mathcal A_{P^{\{\nu_t=v\}}}[Y]$ is $\mathcal A$ applied to the distribution of $Y$ under the conditional probability $P^{\{\nu_t=v\}}=P(\cdot\mid\nu_t=v)$.
--   4. The **optimality values** and **clairvoyant values** at the node $v$ are the sets
--   $$\{\mathcal A_{P^{\{\nu_t=v\}}}[H(x,\xi)] : x\lhd\boldsymbol{\mathcal F},\ x\in\mathcal X\},\qquad \{\mathcal A_{P^{\{\nu_t=v\}}}[H(x,\xi)] : x\lhd\boldsymbol{\mathcal F}^T,\ x\in\mathcal X\},$$
--   whose maxima are $A_t(v)$ and $C_t(v)$. At the root these are the multi-stage problem $A_0$ (5.16) and the clairvoyant's problem $C_0$ (5.17).
--
--   These objects set up the comparison between the decision maker, who must decide on the information available at each stage, and the clairvoyant, who knows the whole scenario from the start; the difference $C_t-A_t$ is the value of information.
--
--   **Formalization Note** The process is indexed by `Fin (T + 1)`; stage $0$ is the root, so that $\mathcal F_0=\sigma(\nu_0)$ is trivial when $\mathcal N_0$ has one point (the theorems assume this). Decisions take values in a measurable space $\mathbb X$, $x$ is `Ω → Fin T → 𝕏` with `x ω i` $=x_i(\omega)$, and $x\in\mathcal X$ is required for every $\omega$. In `H x ξ` the scenario argument is `ξ : Fin T → Ξ` with `ξ i` $=\xi_{i+1}=f_i(\nu_{i+1})$, so `H x ξ` stands for $H(x_0,\xi_1,\dots,x_{T-1},\xi_T)$ in the book's interleaved order. $P^{\{\nu_t=v\}}$ is Mathlib's `P[|ν t ⁻¹' {v}]` (`ProbabilityTheory.cond`), and $\mathcal A_{P^{\{\nu_t=v\}}}[Y]$ is `𝒜` of the image measure `(P[|ν t ⁻¹' {v}]).map Y`. The maxima themselves are not defined here: the theorems take $A_t(v)$, $C_t(v)$ as given numbers and assume each is the greatest element of its set.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 221–223, Eqs. (5.13)–(5.17) and the definitions of A_t(v), C_t(v) on p. 223

import Mathlib

namespace RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {N : Fin (T + 1) → Type*}
  [∀ t, MeasurableSpace (N t)] {Ξ 𝕏 : Type*} [MeasurableSpace 𝕏]

/-- The profit `H(x, ξ) = H(x₀, ξ₁, x₁, …, x_{T−1}, ξ_T)` as a random variable (Pflug & Römisch,
*Modeling, Measuring and Managing Risk*, World Scientific 2007, pp. 221–222, (5.15)–(5.16)).
The tree process is `ν_t`, `t = 0, …, T` (stage `0` is the root), the scenario variables are
`ξ_t = f_t(ν_t)`, `t = 1, …, T`, and `x(ω) = (x₀(ω), …, x_{T−1}(ω))` is the decision sequence.
In Lean `H x ξ` takes the decisions as `x : Fin T → 𝕏` (`x i = x_i`) and the scenarios as
`ξ : Fin T → Ξ` (`ξ i = ξ_{i+1} = f i (ν_{i+1})`). -/
def profit (ν : (t : Fin (T + 1)) → Ω → N t) (f : (i : Fin T) → N i.succ → Ξ)
    (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ) (x : Ω → Fin T → 𝕏) : Ω → ℝ :=
  fun ω => H (x ω) (fun i => f i (ν i.succ ω))

/-- Non-anticipativity `x ◁ 𝓕` (p. 221; p. 119): the decision `x_i` is measurable with respect to
`ℱ_i = σ(ν_i)` of the standard filtration `𝓕 = (ℱ₀, …, ℱ_T)` (5.13), for `i = 0, …, T − 1`. -/
def IsNonanticipative (ν : (t : Fin (T + 1)) → Ω → N t) (x : Ω → Fin T → 𝕏) : Prop :=
  ∀ i : Fin T,
    Measurable[MeasurableSpace.comap (ν i.castSucc) inferInstance] (fun ω => x ω i)

/-- `x ◁ 𝓕^T` (p. 222, (5.17)): every decision `x_i` is measurable with respect to `ℱ_T = σ(ν_T)`,
the clairvoyant's filtration `𝓕^T = (ℱ_T, …, ℱ_T)` (5.14). -/
def IsClairvoyantAdapted (ν : (t : Fin (T + 1)) → Ω → N t) (x : Ω → Fin T → 𝕏) : Prop :=
  ∀ i : Fin T,
    Measurable[MeasurableSpace.comap (ν (Fin.last T)) inferInstance] (fun ω => x ω i)

/-- `𝒜_{P^{ν_t = v}}[Y]` (p. 223): the version-independent functional `𝒜` (a map on distributions
on `ℝ`) applied to the distribution of `Y` under the conditional probability
`P^{ν_t = v} = P(· | ν_t = v)`. -/
noncomputable def condAcceptability (𝒜 : Measure ℝ → ℝ) (P : Measure Ω)
    (ν : (t : Fin (T + 1)) → Ω → N t) (t : Fin (T + 1)) (v : N t) (Y : Ω → ℝ) : ℝ :=
  𝒜 ((P[|ν t ⁻¹' {v}]).map Y)

/-- The values `𝒜_{P^{ν_t = v}}[H(x, ξ)]` over all feasible non-anticipative decisions
`x ◁ 𝓕`, `x ∈ 𝒳` (p. 223); `A_t(v)` is the maximum of this set. -/
def optimalityValues (𝒜 : Measure ℝ → ℝ) (P : Measure Ω) (ν : (t : Fin (T + 1)) → Ω → N t)
    (f : (i : Fin T) → N i.succ → Ξ) (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ)
    (𝒳 : Set (Fin T → 𝕏)) (t : Fin (T + 1)) (v : N t) : Set ℝ :=
  {a | ∃ x : Ω → Fin T → 𝕏, IsNonanticipative ν x ∧ (∀ ω, x ω ∈ 𝒳) ∧
    a = condAcceptability 𝒜 P ν t v (profit ν f H x)}

/-- The values `𝒜_{P^{ν_t = v}}[H(x, ξ)]` over all feasible clairvoyant decisions
`x ◁ 𝓕^T`, `x ∈ 𝒳` (p. 223); `C_t(v)` is the maximum of this set. -/
def clairvoyantValues (𝒜 : Measure ℝ → ℝ) (P : Measure Ω) (ν : (t : Fin (T + 1)) → Ω → N t)
    (f : (i : Fin T) → N i.succ → Ξ) (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ)
    (𝒳 : Set (Fin T → 𝕏)) (t : Fin (T + 1)) (v : N t) : Set ℝ :=
  {a | ∃ x : Ω → Fin T → 𝕏, IsClairvoyantAdapted ν x ∧ (∀ ω, x ω ∈ 𝒳) ∧
    a = condAcceptability 𝒜 P ν t v (profit ν f H x)}

end RiskFunctionals.ValueOfInfo


