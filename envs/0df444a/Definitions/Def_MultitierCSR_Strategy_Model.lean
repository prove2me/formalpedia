-- Prove2me | Definitions.Def_MultitierCSR_Strategy_Model
-- name    : MultitierCSR_Strategy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:16.402138+00:00
-- url     : https://prove2.me/theorems/96502b4c-a91e-4cf5-b369-f3a9a913a8d6
-- title:
--   §3, pp. 7–12, eq. (1), Table 2 — three-tier responsibility-effort model
-- statement:
--   A fixed supply chain contains a Tier 0 buyer and Tier 1 and Tier 2 suppliers. Tier $i$ has margin $m_i$, effort cost $k_i x_i$, and loss $\ell_i=\gamma m_i d+a_i$ when a Tier 2 violation is detected. Demand is $d$. Total effort is $x_2(x_0+x_1+b)$, actual violation probability is $\lambda=e^{-x_2(x_0+x_1+b)}$, and detection conditional on a violation has probability $\beta$. Thus detected violation probability is $\alpha=\beta\lambda$, and expected profit is
--
--   $$
--   \Pi_i(x_0,x_1,x_2)=m_i d-k_i x_i-\ell_i\alpha,\qquad \tau_i=k_i/\ell_i.
--   $$
--
--   The model defines the three rows of Table 2, their effort levels and actual violation probabilities, and the threshold $g(\tau_0)=(b\tau_0/(2\sqrt{\tau_0}-\sqrt{\tau_1}))^2$ used in Theorem 1.
--
--   **Formalization Note** The standing regime has $d>0$, $m_i\ge0$, $a_i\ge0$, $k_i>0$, $\ell_i>0$, $0<\gamma<1$, $0<\beta\le1$, $b>0$, and $b>\tau_2/\beta$. The positive demand, nonnegative indirect losses, positive total losses and positive detection probability make implicit economic or division conventions explicit. Strategies and optimality are inherited from the separate sequential-game interface. Table rows are formulas; they are not definitions of best responses.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), pp. 7–14 (PDF 7–14), §3, eq. (1), Tables 1–2

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_SequentialEffortGame

namespace MultitierCSR.Strategy

noncomputable section

/-- Parameters of the fixed three-tier supply chain of §3. -/
structure Params where
  d : ℝ
  m0 : ℝ
  m1 : ℝ
  m2 : ℝ
  γ : ℝ
  a0 : ℝ
  a1 : ℝ
  a2 : ℝ
  k0 : ℝ
  k1 : ℝ
  k2 : ℝ
  β : ℝ
  b : ℝ

def Params.ell0 (P : Params) : ℝ := P.γ * P.m0 * P.d + P.a0
def Params.ell1 (P : Params) : ℝ := P.γ * P.m1 * P.d + P.a1
def Params.ell2 (P : Params) : ℝ := P.γ * P.m2 * P.d + P.a2

def Params.tau0 (P : Params) : ℝ := P.k0 / P.ell0
def Params.tau1 (P : Params) : ℝ := P.k1 / P.ell1
def Params.tau2 (P : Params) : ℝ := P.k2 / P.ell2

/-- The §3 parameter regime, including the disclosed positivity assumptions needed for ratios. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.d ∧ 0 ≤ P.m0 ∧ 0 ≤ P.m1 ∧ 0 ≤ P.m2 ∧
  0 < P.γ ∧ P.γ < 1 ∧
  0 ≤ P.a0 ∧ 0 ≤ P.a1 ∧ 0 ≤ P.a2 ∧
  0 < P.k0 ∧ 0 < P.k1 ∧ 0 < P.k2 ∧
  0 < P.ell0 ∧ 0 < P.ell1 ∧ 0 < P.ell2 ∧
  0 < P.β ∧ P.β ≤ 1 ∧ 0 < P.b ∧ P.tau2 / P.β < P.b

/-- Probability λ of an actual Tier 2 violation. -/
def violationProb (P : Params) (x0 x1 x2 : ℝ) : ℝ :=
  Real.exp (-(x2 * (x0 + x1 + P.b)))

/-- Probability α that a violation occurs and is detected. -/
def detectedProb (P : Params) (x0 x1 x2 : ℝ) : ℝ :=
  P.β * violationProb P x0 x1 x2

def profit0 (P : Params) (x0 x1 x2 : ℝ) : ℝ :=
  P.m0 * P.d - P.k0 * x0 - P.ell0 * detectedProb P x0 x1 x2
def profit1 (P : Params) (x0 x1 x2 : ℝ) : ℝ :=
  P.m1 * P.d - P.k1 * x1 - P.ell1 * detectedProb P x0 x1 x2
def profit2 (P : Params) (x0 x1 x2 : ℝ) : ℝ :=
  P.m2 * P.d - P.k2 * x2 - P.ell2 * detectedProb P x0 x1 x2

/-- The paper's three-tier game as an instance of a sequential effort game. -/
def Params.game (P : Params) : SequentialEffortGame :=
  ⟨profit0 P, profit1 P, profit2 P⟩

def IsBestResponse2 (P : Params) (σ2 : ℝ → ℝ → ℝ) : Prop :=
  P.game.IsBestResponse2 σ2
def IsBestResponse1 (P : Params) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ) : Prop :=
  P.game.IsBestResponse1 σ2 σ1
def buyerProfit (P : Params) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ) (x0 : ℝ) : ℝ :=
  P.game.buyerProfit σ2 σ1 x0
def IsBuyerOptimal (P : Params) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (x0 : ℝ) : Prop :=
  P.game.IsBuyerOptimal σ2 σ1 x0

/-- The indicated row is the unique selected equilibrium choice and has the stated risk. -/
def ChoiceIs (P : Params) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (e0 e1 e2 lam : ℝ) : Prop :=
  IsBuyerOptimal P σ2 σ1 e0 ∧
  (∀ x0, IsBuyerOptimal P σ2 σ1 x0 → x0 = e0) ∧
  σ1 e0 = e1 ∧ σ2 e0 e1 = e2 ∧ violationProb P e0 e1 e2 = lam

def ChoiceRow (P : Params) (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (r : ℝ × ℝ × ℝ × ℝ) : Prop :=
  ChoiceIs P σ2 σ1 r.1 r.2.1 r.2.2.1 r.2.2.2

/-- The candidate Tier 2 effort from Lemma 1. Its optimality is a theorem, not a definition. -/
def tier2Candidate (P : Params) (x0 x1 : ℝ) : ℝ :=
  Real.log (P.β * (x0 + x1 + P.b) / P.tau2) / (x0 + x1 + P.b)

/-- The candidate Tier 1 effort from Lemma 2. -/
def tier1Candidate (P : Params) (x0 : ℝ) : ℝ :=
  max (Real.sqrt (P.tau2 / P.tau1) - P.b - x0) 0

/-- Table 2: no effort by Tiers 0 and 1. Tuple entries are x₀, x₁, x₂, λ. -/
def noEffortRow (P : Params) : ℝ × ℝ × ℝ × ℝ :=
  (0, 0, Real.log (P.β * P.b / P.tau2) / P.b,
    P.tau2 / (P.β * P.b))

/-- Table 2: Tier 1 carries downstream effort. -/
def delegationRow (P : Params) : ℝ × ℝ × ℝ × ℝ :=
  (0, Real.sqrt (P.tau2 / P.tau1) - P.b,
    Real.sqrt (P.tau1 / P.tau2) *
      Real.log (P.β / Real.sqrt (P.tau1 * P.tau2)),
    Real.sqrt (P.tau1 * P.tau2) / P.β)

/-- Table 2: Tier 0 carries downstream effort. -/
def controlRow (P : Params) : ℝ × ℝ × ℝ × ℝ :=
  (Real.sqrt (P.tau2 / P.tau0) - P.b, 0,
    Real.sqrt (P.tau0 / P.tau2) *
      Real.log (P.β / Real.sqrt (P.tau0 * P.tau2)),
    Real.sqrt (P.tau0 * P.tau2) / P.β)

/-- The threshold g(τ₀) of Theorem 1(i)(b), used where τ₀ > τ₁/4. -/
def g (P : Params) : ℝ :=
  (P.b * P.tau0 / (2 * Real.sqrt P.tau0 - Real.sqrt P.tau1)) ^ 2

end
end MultitierCSR.Strategy


