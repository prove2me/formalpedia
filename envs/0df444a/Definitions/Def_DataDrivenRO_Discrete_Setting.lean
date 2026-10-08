-- Prove2me | Definitions.Def_DataDrivenRO_Discrete_Setting
-- name    : DataDrivenRO_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:26:25.246193+00:00
-- url     : https://prove2.me/theorems/1decc9b6-7bc2-4b08-b047-6dfd6c425191
-- title:
--   Finite-support laws, CVaR and the χ² and G regions of (10)–(13)
-- statement:
--   Fix listed support vectors $a_0,\ldots,a_{n-1}\in\mathbb R^d$. A probability vector $p\in\Delta_n$ gives the finite-support law $P_p=\sum_j p_j\delta_{a_j}$. For a direction $v$ and tail level $\epsilon$, this file uses the published value-at-risk definition at cumulative level $1-\epsilon$ and defines conditional value at risk by
--
--   $$
--   \operatorname{CVaR}^{P_p}_{\epsilon}(v)
--     =\inf_{t\in\mathbb R}\left[t+\frac1\epsilon\sum_jp_j(a_j^{\mathsf T}v-t)^+\right].
--   $$
--
--   The auxiliary set $U^{\operatorname{CVaR}_{P_p}}_\epsilon$ consists of $\sum_jq_ja_j$ with $q\in\Delta_n$ and $q_j\le p_j/\epsilon$. The Pearson and G confidence regions constrain a candidate $p\in\Delta_n$ by, respectively, $\sum_j(p_j-\hat p_j)^2/(2p_j)\le\rho$ and $D(\hat p,p)\le\rho$. Finally, $U^{\chi^2}_\epsilon$ and $U^G_\epsilon$ use the same $q$ constraint for some $p$ in the corresponding region. These are the objects used by Theorem 4 and its companion theorem EC.1.
--
--   **Formalization Note** The index set is `Fin n`, with zero-based coordinates. A zero denominator with a positive numerator has infinite divergence in the source, so both regions impose absolute-continuity side conditions. The $G$ region uses the published finite-vector formula for $D$ with this guard. The real infimum for CVaR equals the displayed minimum on $p\in\Delta_n$ and $0<\epsilon<1$; its value outside that domain is not used in the statements.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (10)–(13), pp. 12–13; (EC.1), p. ec2

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_EntropyInner_klBall

open MeasureTheory

namespace DataDrivenRO.Discrete

/-- The law supported on the listed points, with weights `p`.  Equation (10), p. 12. -/
noncomputable def pointLaw {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ) :
    Measure (Fin d → ℝ) :=
  ∑ j, ENNReal.ofReal (p j) • Measure.dirac (a j)

/-- Value at Risk (6), p. 10, for a linear loss under the finite-support law. -/
noncomputable def VaR {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk (pointLaw a p) (fun u => u ⬝ᵥ v) (1 - ε)

/-- Conditional Value at Risk (11), p. 12, written as the infimum of its attained minimum. -/
noncomputable def CVaR {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  sInf (Set.range (fun t : ℝ =>
    t + (1 / ε) * ∑ j, p j * max (a j ⬝ᵥ v - t) 0))

/-- The finite-support CVaR uncertainty set (EC.1), p. ec2. -/
def cvarSet {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ q ∈ stdSimplex ℝ (Fin n),
    (∀ j, q j ≤ p j / ε) ∧ u = ∑ j, q j • a j}

/-- Pearson's chi-square confidence region (10), p. 12.  The side condition gives the
source's infinite value when `p i = 0` and `phat i > 0`. -/
def chi2Region {n : ℕ} (phat : Fin n → ℝ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Fin n) ∧
    (∀ i, p i = 0 → phat i = 0) ∧
    (∑ i, (p i - phat i) ^ 2 / (2 * p i)) ≤ ρ}

/-- The G-test confidence region (10), p. 12.  The side condition gives infinite divergence
when `phat i > 0` and `p i = 0`; the zero-numerator contribution is zero. -/
def gRegion {n : ℕ} (phat : Fin n → ℝ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Fin n) ∧
    (∀ i, 0 < phat i → 0 < p i) ∧
    RobustMDP.EntropyInner.klDiv phat p ≤ ρ}

/-- The chi-square uncertainty set (12), p. 13. -/
def Uchi2 {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (phat : Fin n → ℝ)
    (ρ ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ q ∈ stdSimplex ℝ (Fin n), ∃ p ∈ chi2Region phat ρ,
    (∀ j, q j ≤ p j / ε) ∧ u = ∑ j, q j • a j}

/-- The G-test uncertainty set (13), p. 13. -/
def UG {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (phat : Fin n → ℝ)
    (ρ ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ q ∈ stdSimplex ℝ (Fin n), ∃ p ∈ gRegion phat ρ,
    (∀ j, q j ≤ p j / ε) ∧ u = ∑ j, q j • a j}

end DataDrivenRO.Discrete


