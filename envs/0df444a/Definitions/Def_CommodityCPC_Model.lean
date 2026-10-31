-- Prove2me | Definitions.Def_CommodityCPC_Model
-- name    : CommodityCPC_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:51.623712+00:00
-- url     : https://prove2.me/theorems/bd1ebcf8-9e76-40b8-86e2-259510d45fe7
-- title:
--   The commodity procurement model of §3: parameters, $\lambda_i,\beta,\kappa,\theta^T_A,\theta^T_B$, Gaussian noises, signals, Cournot subgames, profits
-- statement:
--   Two firms $A,B$ order a commodity and resell it in one market. Firm $i$, with rival $j$, faces the market-clearing price $p_i=a+\varepsilon_a-q_i-\gamma q_j$ with $\gamma\in[0,1]$. Under the **fixed-price contract** (FPC) it pays the known price $w$. Under the **contingent-price contract** (CPC) it pays $s=\mu_s+\varepsilon_s$. Its realized profit is $\pi_i=(p_i-s)q_i$ under the CPC and $\pi_i=(p_i-w)q_i$ under the FPC.
--
--   **Parameters.** A structure holds $a,\mu_s,w\in\mathbb R$, the standard deviations $\sigma_a,\sigma_A,\sigma_B>0$, the demand-price correlation $\rho\in[0,1)$, the forecast correlation $\eta\in[0,1)$, and $\gamma\in[0,1]$. The relative price volatility $\theta=\sigma_s/\sigma_a$ is a separate argument of every object, so that $\sigma_s=\theta\sigma_a$ is derived and $\theta$ can vary with everything else held fixed.
--
--   **Derived constants.**
--
--   $$
--   \lambda_i=\frac{\sigma_a^2}{\sigma_a^2+\sigma_i^2},\qquad \beta=\frac{\eta\sigma_A\sigma_B}{\sigma_a^2},\qquad \kappa=\frac{1}{4-\gamma^2\lambda_A\lambda_B(1+\beta)^2},
--   $$
--
--   $$
--   \theta^T_A=\frac{-2+\gamma\lambda_B(1+\beta)}{\rho\gamma\lambda_B(1+\beta)},\qquad \theta^T_B=\frac{2-\gamma\lambda_A(1+\beta)}{2\rho}.
--   $$
--
--   **Noises.** The state space is $\mathbb R^4$ with the product of four standard normal laws, with coordinates $Z_0,\dots,Z_3$. Then $\varepsilon_a=\sigma_aZ_0$, $\varepsilon_s=\sigma_s(\rho Z_0+\sqrt{1-\rho^2}Z_1)$, $\varepsilon_A=\sigma_AZ_2$, $\varepsilon_B=\sigma_B(\eta Z_2+\sqrt{1-\eta^2}Z_3)$, and firm $i$'s signal is $f_i=\varepsilon_a+\varepsilon_i$.
--
--   **Subgames.** A subgame assigns a contract to each firm: CC, CF, FC or FF, with the first letter firm $A$'s. Each subgame at each $\theta$ is a Bayesian game in the sense of `CommodityCPC.BayesianGame`, with signals $f_i$ and payoffs $\pi_i$. The ex ante profit $\Pi_i$ at a strategy profile is the expectation of $\pi_i$.
--
--   This module carries the model on which every statement of the mission rests. The equilibrium and the profit are primitives: neither is defined through the closed forms (1)–(8) of the paper.
--
--   **Formalization Note** The canonical space realizes the paper's joint law, with $(\varepsilon_A,\varepsilon_B)$ independent of $(\varepsilon_a,\varepsilon_s)$. All divisions are safe under the standing assumptions: $\sigma_a>0$ for $\lambda_i$ and $\beta$, the milestone `CommodityCPC.kappa_pos` for $\kappa$, and $\rho>0$ with $\gamma\neq0$ for the thresholds, which are used only there. The realized profit is integrable at every admissible profile. The module holds several tightly coupled definitions.
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), §3, pp. 9–12 and Table 1; κ §4.1, p. 12; θ^T eq. (9), p. 15; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib
import Definitions.Def_CommodityCPC_BayesianGame

namespace CommodityCPC

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The two importing firms `A` and `B`, Xing–Liu–Zhang–Zhao, *The Bright Side of Price Volatility
in Global Commodity Procurement*, SSRN 4717149 (2023-12-27), Management Science (2024),
doi:10.1287/mnsc.2023.00304, §3, p. 9. -/
inductive Firm
  | A
  | B
  deriving DecidableEq

/-- The rival `j` of firm `i`. -/
def Firm.other : Firm → Firm
  | .A => .B
  | .B => .A

/-- The two contracts, Xing et al., §3, p. 9: `C`, the contingent-price contract (CPC), and `F`,
the fixed-price contract (FPC). -/
inductive Contract
  | C
  | F
  deriving DecidableEq

/-- A Cournot subgame assigns a contract to each firm, Xing et al., §3, p. 11. -/
abbrev Subgame : Type := Firm → Contract

/-- The `CC` subgame: both firms hold the CPC, Xing et al., p. 11. -/
def CC : Subgame
  | .A => .C
  | .B => .C

/-- The `CF` subgame: firm `A` holds the CPC and firm `B` the FPC, Xing et al., p. 11. -/
def CF : Subgame
  | .A => .C
  | .B => .F

/-- The `FC` subgame: firm `A` holds the FPC and firm `B` the CPC, Xing et al., p. 11. -/
def FC : Subgame
  | .A => .F
  | .B => .C

/-- The `FF` subgame: both firms hold the FPC, Xing et al., p. 11. -/
def FF : Subgame
  | .A => .F
  | .B => .F

/-- **The parameters of the model and their standing assumptions**, Xing et al., §3, pp. 9–10, and
Table 1, p. 12, except the relative price volatility `θ`: every object below takes `θ` as a
separate argument, so that "`θ` varies and nothing else does" is visible in the statements.

**Formalization Note.** `a`, `μs` and `w` carry no sign condition: nothing uses one. The paper's
`λ_i ∈ (0,1)`, p. 10, is the condition `0 < σa`, `0 < σA`, `0 < σB`. The paper's remark that the
standard deviations are "sufficiently smaller" than `a` and `μs`, p. 9, has no formal content
and is not encoded. -/
structure Params where
  /-- Market size `a`. -/
  a : ℝ
  /-- Expected CPC price `μ_s`. -/
  μs : ℝ
  /-- FPC price `w`. -/
  w : ℝ
  /-- Standard deviation `σ_a` of the demand noise. -/
  σa : ℝ
  /-- Standard deviation `σ_A` of firm `A`'s forecast noise. -/
  σA : ℝ
  /-- Standard deviation `σ_B` of firm `B`'s forecast noise. -/
  σB : ℝ
  /-- Demand-price correlation `ρ`. -/
  ρ : ℝ
  /-- Forecast correlation `η`. -/
  η : ℝ
  /-- Competition intensity `γ`. -/
  γ : ℝ
  hσa : 0 < σa
  hσA : 0 < σA
  hσB : 0 < σB
  hρ0 : 0 ≤ ρ
  hρ1 : ρ < 1
  hη0 : 0 ≤ η
  hη1 : η < 1
  hγ0 : 0 ≤ γ
  hγ1 : γ ≤ 1

namespace Params

variable (p : Params)

/-- The forecast noise standard deviation `σ_i` of firm `i`. -/
def σf : Firm → ℝ
  | .A => p.σA
  | .B => p.σB

/-- Forecast accuracy `λ_i ≡ σ_a²/(σ_a² + σ_i²)`, Xing et al., p. 9.

**Formalization Note.** The denominator is positive, because `0 < σa`. -/
def lam (i : Firm) : ℝ := p.σa ^ 2 / (p.σa ^ 2 + p.σf i ^ 2)

/-- `β ≡ ησ_Aσ_B/σ_a²`, Xing et al., p. 11.

**Formalization Note.** The denominator is positive, because `0 < σa`. The paper's second form
`η√((1 − λ_A)(1 − λ_B)/(λ_Aλ_B))` is an identity, not the definition. -/
def β : ℝ := p.η * p.σA * p.σB / p.σa ^ 2

/-- `κ ≡ 1/[4 − γ²λ_Aλ_B(1 + β)²]`, Xing et al., §4.1, p. 12.

**Formalization Note.** The denominator is positive, see `CommodityCPC.kappa_pos`. -/
def κ : ℝ := 1 / (4 - p.γ ^ 2 * p.lam .A * p.lam .B * (1 + p.β) ^ 2)

/-- The threshold `θ^T_A = (−2 + γλ_B(1 + β))/(ργλ_B(1 + β))` of eq. (9), Xing et al., p. 15.

**Formalization Note.** Used only under `0 < ρ` and `γ ≠ 0`; then the denominator is positive,
because `0 ≤ γ`, `0 < λ_B` and `0 ≤ β`. It is independent of `θ`. -/
def θTA : ℝ := (-2 + p.γ * p.lam .B * (1 + p.β)) / (p.ρ * p.γ * p.lam .B * (1 + p.β))

/-- The threshold `θ^T_B = (2 − γλ_A(1 + β))/(2ρ)` of eq. (9), Xing et al., p. 15.

**Formalization Note.** Used only under `0 < ρ`, so the denominator is positive. It is
independent of `θ`. -/
def θTB : ℝ := (2 - p.γ * p.lam .A * (1 + p.β)) / (2 * p.ρ)

/-- The state space: four independent standard normal coordinates `Z₀, Z₁, Z₂, Z₃`. -/
abbrev Ω : Type := Fin 4 → ℝ

/-- The price standard deviation `σ_s ≡ θσ_a`, Xing et al., p. 11. `θ` is the parameter, `σ_s` is
derived from it. -/
def σs (θ : ℝ) : ℝ := θ * p.σa

/-- The demand noise `ε_a = σ_a Z₀ ∼ N[0, σ_a²]`, Xing et al., p. 9. -/
def εa (ω : Ω) : ℝ := p.σa * ω 0

/-- The CPC price noise `ε_s = σ_s(ρZ₀ + √(1 − ρ²)Z₁) ∼ N[0, σ_s²]`, correlated `ρ` with `ε_a`,
Xing et al., p. 9. -/
def εs (θ : ℝ) (ω : Ω) : ℝ :=
  p.σs θ * (p.ρ * ω 0 + Real.sqrt (1 - p.ρ ^ 2) * ω 1)

/-- The forecast noises `ε_A = σ_A Z₂` and `ε_B = σ_B(ηZ₂ + √(1 − η²)Z₃)`: `ε_i ∼ N[0, σ_i²]`,
correlated `η` with each other, and independent of `(ε_a, ε_s)`, Xing et al., p. 9. -/
def εf : Firm → Ω → ℝ
  | .A, ω => p.σA * ω 2
  | .B, ω => p.σB * (p.η * ω 2 + Real.sqrt (1 - p.η ^ 2) * ω 3)

/-- The CPC price `s = μ_s + ε_s`, Xing et al., p. 9. -/
def s (θ : ℝ) (ω : Ω) : ℝ := p.μs + p.εs θ ω

/-- Firm `i`'s private demand forecast `f_i = ε_a + ε_i`, Xing et al., p. 9. -/
def signal (i : Firm) (ω : Ω) : ℝ := p.εa ω + p.εf i ω

/-- The σ-algebra generated by the signal `f_i`. -/
abbrev signalAlgebra (i : Firm) : MeasurableSpace Ω :=
  MeasurableSpace.comap (p.signal i) inferInstance

/-- The market-clearing price `p_i = a + ε_a − q_i − γq_j` of firm `i`, Xing et al., p. 9. -/
def price (i : Firm) (q : Firm → ℝ) (ω : Ω) : ℝ :=
  p.a + p.εa ω - q i - p.γ * q i.other

/-- Firm `i`'s unit cost in the subgame `k`: the CPC price `s` under the CPC and the FPC price `w`
under the FPC, Xing et al., p. 10. -/
def cost (θ : ℝ) (k : Subgame) (i : Firm) (ω : Ω) : ℝ :=
  match k i with
  | .C => p.s θ ω
  | .F => p.w

/-- Firm `i`'s realized profit `π_i = (p_i − c_i)q_i`, with `c_i = s` under the CPC and `c_i = w`
under the FPC, Xing et al., p. 10. -/
def profit (θ : ℝ) (k : Subgame) (i : Firm) (q : Firm → ℝ) (ω : Ω) : ℝ :=
  (p.price i q ω - p.cost θ k i ω) * q i

end Params

/-- The prior: the product of four standard normal laws on `Ω = ℝ⁴`.

**Formalization Note.** This canonical space realizes the joint law of Xing et al., p. 9:
`(ε_a, ε_s) ∼ BN[0, 0, σ_a², σ_s², ρ]`, `ε_i ∼ N[0, σ_i²]`, `(ε_A, ε_B)` bivariate normal with
correlation `η` and independent of `(ε_a, ε_s)`. The paper's sentence "`ε_A` and `ε_B` are
independent of `ε_a` and `ε_s`" is read as the independence of the two pairs, all four noises
being jointly Gaussian; `E[f_j | f_i]` in Lemma 1 needs this. -/
def P : Measure Params.Ω := Measure.pi fun _ => gaussianReal 0 1

namespace Params

variable (p : Params)

/-- **The Cournot subgame `k` at the relative price volatility `θ`**, Xing et al., §3, pp. 9–11:
a Bayesian game of the firms `A`, `B`, with signals `f_i` and realized profits `π_i`.

**Formalization Note.** The price noise has standard deviation `σ_s = θσ_a` and every other
parameter is held in `p`. The realized profit is a polynomial of degree two in the noises and the
quantities, so it is integrable at every admissible profile, and the ex ante profit is a genuine
expectation. -/
def game (θ : ℝ) (k : Subgame) : BayesianGame Firm Ω where
  P := P
  signal := p.signal
  payoff := p.profit θ k

/-- `Π_i`: the ex ante profit of firm `i` at the strategy profile `σ` in the subgame `k`, the
expectation of the realized profit `π_i`, Xing et al., Table 1, p. 12, and §4.2, p. 14.

**Formalization Note.** The paper's `Π^k_i` is this quantity at the equilibrium of the subgame.
It is defined here at an arbitrary profile, and the equilibrium is not presupposed: the closed
forms (6)–(8) are theorems about it. -/
def exAnteProfit (θ : ℝ) (k : Subgame) (i : Firm) (σ : Firm → ℝ → ℝ) : ℝ :=
  (p.game θ k).exAntePayoff i σ

end Params

end

end CommodityCPC


