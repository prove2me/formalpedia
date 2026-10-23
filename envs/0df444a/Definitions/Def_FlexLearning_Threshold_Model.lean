-- Prove2me | Definitions.Def_FlexLearning_Threshold_Model
-- name    : FlexLearning_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:08.458772+00:00
-- url     : https://prove2.me/theorems/aaa64efc-55e8-4c11-924b-2e8befb94a5a
-- title:
--   §2.1–§3, pp. 6–11 — two-product capacity model: dedicated vs priority-fulfilment flexible capacity, uniform prior, censored-sales posteriors, two-period values (ξ = 0)
-- statement:
--   This file sets up the two-product, two-period capacity model of Chod, Markakis and Trichakis in the symmetric case of their §3, with second-period demand equal to first-period demand.
--
--   **Data.** A price $p$, a unit cost $c$ of dedicated (product-specific) capacity, a unit cost $c_F$ of flexible capacity, and the support $[x, x+U]$ of each product's demand. The first-period demands $(D^1_1, D^1_2)$ are independent and each uniform on $[x, x+U]$:
--   $$\mathbb P = \mathrm{Unif}[x,x+U] \otimes \mathrm{Unif}[x,x+U].$$
--
--   **Static model (§2.1).**
--   1. *Non-flexible system.* Dedicated capacities $\mathbf Q = (Q_1, Q_2)$ give sales $S_{N,i} = \min\{D_i, Q_i\}$ and expected profit $\pi_N(\mathbf Q) = p\,\mathbb E[S_{N,1} + S_{N,2}] - c(Q_1 + Q_2)$, Eqs. (1)–(2).
--   2. *Flexible system.* A single flexible capacity $Q_F$ serves product 1 first: $S_{F,1} = \min\{D_1, Q_F\}$, $S_{F,2} = \min\{D_2, Q_F - S_{F,1}\}$, Eq. (4), with expected profit $\pi_F(c_F)(Q_F) = p\,\mathbb E[S_{F,1} + S_{F,2}] - c_F Q_F$, Eq. (5).
--   3. The optimal static profits are $\bar\pi_N = \sup_{\mathbf Q \in \mathbb R^2_+} \pi_N(\mathbf Q)$ and $\bar\pi_F(c_F) = \sup_{Q_F \ge 0} \pi_F(c_F)(Q_F)$. A unit cost $c_F$ is a **break-even cost of flexibility** when $\bar\pi_F(c_F) = \bar\pi_N$, Eq. (8).
--
--   **Learning from censored sales (§2.2).** A product with $q$ units of capacity available and realized demand $d$ has posterior law $\delta_d$ if $d < q$ (demand observed exactly) and $\mathrm{Unif}[x,x+U]$ conditioned on $\{D \ge q\}$ otherwise (stock-out). The joint posterior is the product of the two products' posteriors. In the non-flexible system product $i$ has $Q_i$ units available; in the flexible system product 1 has $Q_F$ and product 2 has $Q_F - S_{F,1}$.
--
--   **Two-period values (§2.2).** Second-period capacity is dedicated in both systems, Eqs. (10)–(11):
--   $$V^2(\mathbb G) = \sup_{\mathbf Q \in \mathbb R^2_+} \mathbb E_{\mathbb G}\big[p\min\{D_1,Q_1\} + p\min\{D_2,Q_2\} - c(Q_1+Q_2)\big].$$
--   The first-period objectives are $v_N(\mathbf Q) = \pi_N(\mathbf Q) + \mathbb E[V^2(\mathbb P(\cdot\mid \mathbf S^1_N))]$ and $v_F(Q_F) = \pi_F(c_F)(Q_F) + \mathbb E[V^2(\mathbb P(\cdot\mid \mathbf S^1_F))]$, Eq. (16), and the two-period optimal profits are
--   $$V_N = \sup_{\mathbf Q \in \mathbb R^2_+} v_N(\mathbf Q), \qquad V_F(c_F) = \sup_{Q_F \ge 0} v_F(Q_F).$$
--   Finally $\tilde p = \tfrac12\big(2c_F - c + \sqrt{5c^2 - 4cc_F + 4c_F^2}\big)$ is the price threshold of the proof of Proposition 1.
--
--   This model is shared by every statement of the mission; the values are defined as suprema of the Bellman objectives, never by their closed forms.
--
--   **Formalization Note** Second-period demand equals first-period demand ($\xi = 0$ in Eq. (9)); at $x = 0$, the case of Proposition 1, the noise $\epsilon_i \sim U[-\xi x, \xi x]$ vanishes for every $\xi$. The uniform law is $U^{-1}$ times Lebesgue measure on $[x, x+U]$, a probability measure only for $U > 0$, which every theorem assumes. Ties follow p. 9: demand is observed exactly iff it is strictly below the available capacity. The stock-out posterior is Mathlib's conditional measure `cond`. Suprema are real `sSup` of images; the statements are made only under hypotheses that make these sets nonempty and bounded above.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), pp. 6–11 (PDF 6–11), §2.1, §2.2, §3, Eqs. (1)–(12), (16) on p. A5 (PDF 38), p̃ on p. A6 (PDF 39)

import Mathlib

namespace FlexLearning.Threshold

open MeasureTheory ProbabilityTheory

/-- Prior law of one product's first-period demand: uniform on `[x, x + U]` (§3, p. 11).
It is a probability measure when `U > 0`. -/
noncomputable def prior (x U : ℝ) : Measure ℝ :=
  (ENNReal.ofReal U)⁻¹ • volume.restrict (Set.Icc x (x + U))

/-- Joint first-period law of `(D¹₁, D¹₂)`: independent, identically distributed products. -/
noncomputable def prior2 (x U : ℝ) : Measure (ℝ × ℝ) :=
  (prior x U).prod (prior x U)

/-- Expected one-period newsvendor profit with price `p`, unit cost `c`, capacity `Q`,
against a demand law `G`, no salvage value (Lemma 3, p. A3). -/
noncomputable def nvProfit (p c : ℝ) (G : Measure ℝ) (Q : ℝ) : ℝ :=
  ∫ d, (p * min d Q - c * Q) ∂G

/-- Posterior law of one product's demand after first-period sales, when `q` capacity units
were available to it and its demand turned out to be `d` (§2.2, p. 9): if `d < q` the demand
is observed exactly; otherwise the firm stocks out and conditions the prior on `{D ≥ q}`. -/
noncomputable def post (x U q d : ℝ) : Measure ℝ :=
  if d < q then Measure.dirac d else (prior x U)[|Set.Ici q]

/-- Second-period value, Eqs. (10) at `t = 2` and (11): dedicated capacities `Q² ∈ ℝ²₊`
chosen against the belief `G`. Second-period demand equals first-period demand (`ξ = 0`). -/
noncomputable def V2 (p c : ℝ) (G : Measure (ℝ × ℝ)) : ℝ :=
  sSup ((fun Q : ℝ × ℝ => ∫ d, (p * min d.1 Q.1 + p * min d.2 Q.2 - c * (Q.1 + Q.2)) ∂G) ''
    {Q : ℝ × ℝ | 0 ≤ Q.1 ∧ 0 ≤ Q.2})

/-- Static expected profit of the non-flexible system, Eqs. (1)–(2). -/
noncomputable def piN (p c x U : ℝ) (Q : ℝ × ℝ) : ℝ :=
  ∫ d, (p * min d.1 Q.1 + p * min d.2 Q.2) ∂(prior2 x U) - c * (Q.1 + Q.2)

/-- Sales of product 1 in the flexible system, Eq. (4): served first. -/
def salesF1 (QF : ℝ) (d : ℝ × ℝ) : ℝ := min d.1 QF

/-- Sales of product 2 in the flexible system, Eq. (4): served from what product 1 left. -/
def salesF2 (QF : ℝ) (d : ℝ × ℝ) : ℝ := min d.2 (QF - min d.1 QF)

/-- Static expected profit of the flexible system with flexible unit cost `cF`, Eq. (5). -/
noncomputable def piF (p x U cF QF : ℝ) : ℝ :=
  ∫ d, (p * salesF1 QF d + p * salesF2 QF d) ∂(prior2 x U) - cF * QF

/-- Optimal static profit of the non-flexible system, `max_Q π_N`, over `Q ∈ ℝ²₊`. -/
noncomputable def piBarN (p c x U : ℝ) : ℝ :=
  sSup (piN p c x U '' {Q : ℝ × ℝ | 0 ≤ Q.1 ∧ 0 ≤ Q.2})

/-- Optimal static profit of the flexible system, `max_{Q_F} π_F(c_F)`, over `Q_F ≥ 0`. -/
noncomputable def piBarF (p x U cF : ℝ) : ℝ :=
  sSup (piF p x U cF '' Set.Ici 0)

/-- `cF` is a break-even unit cost of flexibility, Eq. (8): the pooling benefits vanish. -/
def IsBreakEven (p c x U cF : ℝ) : Prop :=
  piBarF p x U cF = piBarN p c x U

/-- Two-period objective of the non-flexible system at first-period capacities `Q`,
Eqs. (10) and (16): first-period profit plus the expected second-period value under the
posterior, which is the product of the two products' censored-sales posteriors. -/
noncomputable def vN (p c x U : ℝ) (Q : ℝ × ℝ) : ℝ :=
  piN p c x U Q + ∫ d, V2 p c ((post x U Q.1 d.1).prod (post x U Q.2 d.2)) ∂(prior2 x U)

/-- Two-period optimal profit of the non-flexible system, `V_N = V¹_N(ℙ)`, Eq. (10). -/
noncomputable def VN (p c x U : ℝ) : ℝ :=
  sSup (vN p c x U '' {Q : ℝ × ℝ | 0 ≤ Q.1 ∧ 0 ≤ Q.2})

/-- Two-period objective of the flexible system at first-period flexible capacity `QF`,
Eqs. (12) and (16): product 1 has `QF` units available, product 2 has `QF - S_{F,1}`. -/
noncomputable def vF (p c x U cF QF : ℝ) : ℝ :=
  piF p x U cF QF +
    ∫ d, V2 p c ((post x U QF d.1).prod (post x U (QF - min d.1 QF) d.2)) ∂(prior2 x U)

/-- Two-period optimal profit of the flexible system, `V_F(c_F) = V¹_F(ℙ)`, Eq. (12). -/
noncomputable def VF (p c x U cF : ℝ) : ℝ :=
  sSup (vF p c x U cF '' Set.Ici 0)

/-- The price threshold `p̃` of the proof of Proposition 1, p. A6. -/
noncomputable def pTilde (c cF : ℝ) : ℝ :=
  (2 * cF - c + Real.sqrt (5 * c ^ 2 - 4 * c * cF + 4 * cF ^ 2)) / 2

end FlexLearning.Threshold


