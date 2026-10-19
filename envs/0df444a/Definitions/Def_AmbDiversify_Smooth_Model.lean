-- Prove2me | Definitions.Def_AmbDiversify_Smooth_Model
-- name    : AmbDiversify_Smooth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:27.276546+00:00
-- url     : https://prove2.me/theorems/32324761-1624-436c-bc57-2a35b680530f
-- title:
--   §2–§3.3, pp. 3–11 — one-ship and two-ship lotteries, two-expert SEU and smooth-ambiguity values of diversification, absolute ambiguity aversion
-- statement:
--   The model of Berger and Eeckhoudt's *Risk, ambiguity, and the value of diversification*: Bernoulli's merchant Sempronius, with sure wealth $W_0$, ships commodities of value $L$ either on one ship or split equally over two ships, each ship perishing independently with probability $p$.
--
--   **Risk.** For a von Neumann–Morgenstern utility $u:\mathbb R\to\mathbb R$, the expected utilities without and with diversification are
--   $$EU^{ND} = p\,u(W_0-L) + (1-p)\,u(W_0),\qquad EU^{D} = p^2u(W_0-L) + 2p(1-p)\,u\!\left(W_0-\tfrac L2\right) + (1-p)^2u(W_0),$$
--   and the **value of diversification** is $VD_{risk} = EU^D - EU^{ND}$ (Definition 1). At $p = p_\theta$ this is also $\Delta(\theta)$, the value of diversification according to expert $\theta$.
--
--   **Ambiguity.** Two experts $\theta\in\{1,2\}$ give perishing probabilities $p_1,p_2$, and the decision maker holds the prior $\mu(1)=\mu$, $\mu(2)=1-\mu$. The ambiguity-neutral (two-stage subjective expected utility) evaluations are
--   $$EU^{j}_{AN} = \mu\,EU^{j}(p_1) + (1-\mu)\,EU^{j}(p_2),\quad j\in\{ND,D\},\qquad VD_{AN} = EU^D_{AN}-EU^{ND}_{AN}.$$
--   In the **smooth ambiguity model** with ambiguity function $\phi$,
--   $$EU^{j}_{smt} = \phi^{-1}\big(\mu\,\phi(EU^{j}(p_1)) + (1-\mu)\,\phi(EU^{j}(p_2))\big),\qquad VD_{smt} = EU^D_{smt}-EU^{ND}_{smt}.$$
--   The certainty equivalent $\phi^{-1}(\mu\phi(a)+(1-\mu)\phi(b))$ is denoted $CE_\phi(\mu;a,b)$.
--
--   **Ambiguity attitude.** The coefficient of absolute ambiguity aversion is $\lambda(x) = -\phi''(x)/\phi'(x)$. The decision maker exhibits DAAA, CAAA or IAAA when $\lambda$ is strictly decreasing, constant, or strictly increasing. An **ambiguity function** of an ambiguity-averse decision maker is a twice continuously differentiable $\phi$ with $\phi'>0$ everywhere that is concave.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers, and $u$ and $\phi$ are defined on all of $\mathbb R$ (so, e.g., logarithmic utility is outside the model). $\phi^{-1}$ is `Function.invFun φ`, the true inverse on the range of $\phi$; every argument it receives in the mission is a $\mu$-mixture of two values of $\phi$, which lies in that range for continuous strictly increasing $\phi$ and $\mu\in[0,1]$. The regularity of $\phi$ ($C^2$, $\phi'>0$) is added to the page's "concave function $\phi$", since footnote 7 differentiates $\phi$ twice and (10) inverts it. IAAA/CAAA/DAAA are read as monotonicity of $\lambda$ rather than the sign of $\partial\lambda/\partial x$, which avoids requiring $\phi\in C^3$; a strictly signed derivative implies the monotone form. The values of diversification are differences of the expected utilities (1), (2), (5), (6), (10), not the closed forms (A.1), (A.2), which are milestones.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), pp. 3–11 (PDF 4–12), (1)–(3) and Definition 1 p. 3, (5)–(6) p. 6, (10) p. 10, footnote 7 p. 11; prior weights µ(1) = µ, µ(2) = 1 − µ p. 15 (PDF 16)

import Mathlib

namespace AmbDiversify.Smooth

/-- (1), p. 3: expected utility of sending the commodities of value `L` on one ship that perishes
with probability `p`, from sure wealth `W0`: `p u(W0 − L) + (1 − p) u(W0)`. -/
def EU_ND (u : ℝ → ℝ) (W0 L p : ℝ) : ℝ :=
  p * u (W0 - L) + (1 - p) * u W0

/-- (2), p. 3: expected utility of splitting the commodities over two ships, each carrying `L/2`
and perishing independently with probability `p`:
`p² u(W0 − L) + 2p(1 − p) u(W0 − L/2) + (1 − p)² u(W0)`. -/
noncomputable def EU_D (u : ℝ → ℝ) (W0 L p : ℝ) : ℝ :=
  p ^ 2 * u (W0 - L) + 2 * p * (1 - p) * u (W0 - L / 2) + (1 - p) ^ 2 * u W0

/-- (3), Definition 1, p. 3: the value of diversification under risk, `EU^D − EU^ND`.
At `p = pθ` it is also `∆(θ)` of (12), p. 10, the value of diversification according to expert `θ`. -/
noncomputable def VD_risk (u : ℝ → ℝ) (W0 L p : ℝ) : ℝ :=
  EU_D u W0 L p - EU_ND u W0 L p

/-- (5), p. 6, with the prior `µ(1) = µ`, `µ(2) = 1 − µ` (p. 15): ambiguity-neutral (two-stage SEU)
utility without diversification. -/
def EU_ND_AN (u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) : ℝ :=
  μ * EU_ND u W0 L p1 + (1 - μ) * EU_ND u W0 L p2

/-- (6), p. 6, with `µ(1) = µ`, `µ(2) = 1 − µ`: ambiguity-neutral utility under diversification. -/
noncomputable def EU_D_AN (u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) : ℝ :=
  μ * EU_D u W0 L p1 + (1 - μ) * EU_D u W0 L p2

/-- p. 6: the value of diversification under ambiguity neutrality, `VD_AN = EU^D_AN − EU^ND_AN`. -/
noncomputable def VD_AN (u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) : ℝ :=
  EU_D_AN u W0 L μ p1 p2 - EU_ND_AN u W0 L μ p1 p2

/-- The certainty equivalent of (10): `φ⁻¹(µ φ(a) + (1 − µ) φ(b))`, with `φ⁻¹ = Function.invFun φ`
(the true inverse on the range of `φ`). -/
noncomputable def smoothCE (φ : ℝ → ℝ) (μ a b : ℝ) : ℝ :=
  Function.invFun φ (μ * φ a + (1 - μ) * φ b)

/-- (10), p. 10, `j = ND`: smooth-ambiguity utility without diversification,
`φ⁻¹(Σθ µ(θ) φ(EU^ND(W(θ))))`. -/
noncomputable def EU_ND_smt (φ u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) : ℝ :=
  smoothCE φ μ (EU_ND u W0 L p1) (EU_ND u W0 L p2)

/-- (10), p. 10, `j = D`: smooth-ambiguity utility under diversification,
`φ⁻¹(Σθ µ(θ) φ(EU^D(W(θ))))`. -/
noncomputable def EU_D_smt (φ u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) : ℝ :=
  smoothCE φ μ (EU_D u W0 L p1) (EU_D u W0 L p2)

/-- p. 10: the value of diversification in the smooth model, `VD_smt = EU^D_smt − EU^ND_smt`. -/
noncomputable def VD_smt (φ u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) : ℝ :=
  EU_D_smt φ u W0 L μ p1 p2 - EU_ND_smt φ u W0 L μ p1 p2

/-- Footnote 7, p. 11: the coefficient of absolute ambiguity aversion `λ(x) = −φ''(x)/φ'(x)`. -/
noncomputable def absAmbAversion (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv (deriv φ) x) / deriv φ x

/-- Footnote 7: decreasing absolute ambiguity aversion, `λ` strictly decreasing. -/
def DAAA (φ : ℝ → ℝ) : Prop := StrictAnti (absAmbAversion φ)

/-- Footnote 7: constant absolute ambiguity aversion, `λ` constant. -/
def CAAA (φ : ℝ → ℝ) : Prop := ∀ x y, absAmbAversion φ x = absAmbAversion φ y

/-- Footnote 7: increasing absolute ambiguity aversion, `λ` strictly increasing. -/
def IAAA (φ : ℝ → ℝ) : Prop := StrictMono (absAmbAversion φ)

/-- p. 9: an ambiguity-averse ambiguity function — twice continuously differentiable, with
`φ' > 0` everywhere (so `φ` is strictly increasing and `φ⁻¹` exists), and concave. -/
def IsAmbiguityFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 φ ∧ (∀ x, 0 < deriv φ x) ∧ ConcaveOn ℝ Set.univ φ

end AmbDiversify.Smooth


