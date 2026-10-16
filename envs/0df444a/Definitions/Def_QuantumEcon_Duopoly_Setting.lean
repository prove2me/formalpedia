-- Prove2me | Definitions.Def_QuantumEcon_Duopoly_Setting
-- name    : QuantumEcon_Duopoly_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:41:10.315352+00:00
-- url     : https://prove2.me/theorems/83d72d19-c5e1-4668-bfcf-9849ccad6bb0
-- title:
--   Two-stage quantum–classical Cournot investment game
-- statement:
--   Let firm 1 operate a quantum computer with unit cost $c$, and firm 2 a classical computer with unit cost $c^2$. Both face common demand intercept $a$ and substitution parameter $\gamma\in[0,1]$, with $a>c^2>c>1$. In stage 1 they choose nonnegative investments $x_i$ at cost $B_i x_i^2/2$, where $B_i>0$. In stage 2 they choose nonnegative quantities $q_i$, facing inverse demand $p_i=a+x_i-q_i-\gamma q_j$. The module defines each profit, the Cournot quantity subgame, and subgame-perfect equilibrium through a stage-2 Nash strategy at every feasible investment pair. It also names the interior quantities and investments in equations (3)–(6) and the thresholds used in Lemma 1 and Proposition 2.
--
--   These definitions provide the common model for the paper's claims. **Formalization Note** All parameters are real; firm 2's cost is exactly $c^2$, not an independent parameter. Closed forms are total Lean functions, but the theorem hypotheses exclude zero denominators.
-- source:
--   Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724 (February 2022), PDF p. 8–11, (1)–(6); PDF pp. 24–28, (16)–(17), Lemma 1 and Proposition 2 thresholds

import Mathlib
import Definitions.Def_SupplierAudit_Competition_CournotDuopoly

set_option autoImplicit false

namespace QuantumEcon.Duopoly

noncomputable section

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF pp. 8–10, model. Firm 1 is quantum, with unit cost `c`; firm 2 is
classical, with unit cost `c²`. -/
structure Params where
  a : ℝ
  c : ℝ
  γ : ℝ
  B₁ : ℝ
  B₂ : ℝ

/-- Bova, Goldfarb, Melko, Quantum Economic Advantage, NBER Working Paper No. 29724
(February 2022), PDF pp. 8–10, standing model assumptions: "we assume γ ∈ [0, 1]" (PDF 8);
"We assume that a > c^2 > c > 1" (PDF 9); "B_1 and B_2 are positive coefficients" (PDF 10).
Formalization Note: `c < c²` is kept as printed although it follows from `1 < c`. -/
def Standing (P : Params) : Prop :=
  0 ≤ P.γ ∧ P.γ ≤ 1 ∧ 1 < P.c ∧ P.c < P.c ^ 2 ∧ P.c ^ 2 < P.a ∧
  0 < P.B₁ ∧ 0 < P.B₂

/-- PDF p. 25, proof of Lemma 1: the intercept threshold `a*`.
Formalization Note: the denominator is nonzero under `Standing`. -/
def aStar (P : Params) : ℝ := P.c * (-2 * P.c + P.γ) / (-2 + P.γ)

/-- PDF p. 24, (16)–(17): the common second-order threshold. -/
def Bhh (P : Params) : ℝ := 8 / (-4 + P.γ ^ 2) ^ 2

/-- PDF p. 25, threshold `B̂₁` in the proof of Lemma 1. -/
def Bh₁ (P : Params) : ℝ :=
  4 * (P.a - P.c ^ 2) /
    ((P.c * (2 * P.c - P.γ) + P.a * (-2 + P.γ)) * (-4 + P.γ ^ 2))

/-- PDF p. 25, threshold `B̂₂` in the proof of Lemma 1. -/
def Bh₂ (P : Params) : ℝ :=
  4 * (P.a - P.c) /
    ((-4 + P.γ ^ 2) * (P.a * (-2 + P.γ) + P.c * (2 - P.c * P.γ)))

/-- PDF p. 26, exact sufficient conditions at the conclusion of the proof of Lemma 1.
Formalization Note: `Max` is real `max`, and all three inequalities are strict. -/
def Lemma1Cond (P : Params) : Prop :=
  aStar P < P.a ∧ max (Bh₁ P) (Bhh P) < P.B₁ ∧
    max (Bh₂ P) (Bhh P) < P.B₂

/-- PDF p. 10, (1), firm 1's profit. Investments and quantities are constrained
nonnegative in the equilibrium predicates, not in this algebraic expression. -/
def profit₁ (P : Params) (x₁ q₁ q₂ : ℝ) : ℝ :=
  q₁ * (P.a + x₁ - q₁ - P.γ * q₂) - P.c * q₁ - P.B₁ * x₁ ^ 2 / 2

/-- PDF p. 10, (2), firm 2's profit; the classical unit cost is `c²`. -/
def profit₂ (P : Params) (x₂ q₁ q₂ : ℝ) : ℝ :=
  q₂ * (P.a + x₂ - q₂ - P.γ * q₁) - P.c ^ 2 * q₂ - P.B₂ * x₂ ^ 2 / 2

/-- PDF pp. 10–11, stage-2 quantity competition after investments are observed.
The fixed investment costs are sunk, so they do not affect best responses in quantity.
The referenced Cournot equilibrium requires nonnegative quantities. -/
def IsStage2Nash (P : Params) (x₁ x₂ q₁ q₂ : ℝ) : Prop :=
  SupplierAudit.Competition.IsCournotNash P.γ (P.a + x₁) P.c
    (P.a + x₂) (P.c ^ 2) q₁ q₂

/-- PDF pp. 10–11, two-stage game solved by backward induction: "In the first stage, Firm 1
sets investment x_1 to maximize its profits and Firm 2 sets x_2 to maximize its profit. In the
second stage, Firm 1 sets q_1 to maximize its profits and Firm 2 sets q_2 to maximize its profits." 
Formalization Note: investments are nonnegative; `σ` prescribes a Nash quantity pair
at every feasible investment pair, including off the realized path. -/
def IsSPE (P : Params) (x₁ x₂ : ℝ) (σ : ℝ → ℝ → ℝ × ℝ) : Prop :=
  (∀ y₁ y₂ : ℝ, 0 ≤ y₁ → 0 ≤ y₂ →
    IsStage2Nash P y₁ y₂ (σ y₁ y₂).1 (σ y₁ y₂).2) ∧
  0 ≤ x₁ ∧ 0 ≤ x₂ ∧
  (∀ y₁ : ℝ, 0 ≤ y₁ →
    profit₁ P y₁ (σ y₁ x₂).1 (σ y₁ x₂).2 ≤
      profit₁ P x₁ (σ x₁ x₂).1 (σ x₁ x₂).2) ∧
  (∀ y₂ : ℝ, 0 ≤ y₂ →
    profit₂ P y₂ (σ x₁ y₂).1 (σ x₁ y₂).2 ≤
      profit₂ P x₂ (σ x₁ x₂).1 (σ x₁ x₂).2)

/-- PDF p. 11, (3), firm 1's interior stage-2 quantity. -/
def qStar₁ (P : Params) (x₁ x₂ : ℝ) : ℝ :=
  (-2 * (P.a - P.c + x₁) + (P.a - P.c ^ 2 + x₂) * P.γ) /
    (-4 + P.γ ^ 2)

/-- PDF p. 11, (4), firm 2's interior stage-2 quantity. -/
def qStar₂ (P : Params) (x₁ x₂ : ℝ) : ℝ :=
  (-2 * (P.a - P.c ^ 2 + x₂) + (P.a - P.c + x₁) * P.γ) /
    (-4 + P.γ ^ 2)

/-- PDF p. 11, shared denominator of (5)–(6). -/
def Fden (P : Params) : ℝ :=
  -8 * (2 + P.B₂ * (-4 + P.γ ^ 2)) +
    P.B₁ * (-4 + P.γ ^ 2) * (-8 + P.B₂ * (-4 + P.γ ^ 2) ^ 2)

/-- PDF p. 11, (5), firm 1's interior investment. -/
def xStar₁ (P : Params) : ℝ :=
  4 * (P.a * (4 - P.B₂ * (-2 + P.γ) ^ 2 * (2 + P.γ)) +
    P.c * (-4 + P.B₂ * (-2 + P.c * P.γ) * (-4 + P.γ ^ 2))) / Fden P

/-- PDF p. 11, (6), firm 2's interior investment. -/
def xStar₂ (P : Params) : ℝ :=
  4 * (-4 * P.c ^ 2 - P.B₁ * P.c * (2 * P.c - P.γ) * (-4 + P.γ ^ 2) +
    P.a * (4 - P.B₁ * (-2 + P.γ) ^ 2 * (2 + P.γ))) / Fden P

/-- PDF pp. 27–28, proof of Proposition 2: the exact threshold for firm 1
to invest more. -/
def prop2Threshold (P : Params) : ℝ :=
  (4 * (-1 + P.c) * P.c +
    P.B₁ * (P.c * (2 * P.c - P.γ) + P.a * (-2 + P.γ)) *
      (-4 + P.γ ^ 2)) /
    ((-4 + P.γ ^ 2) *
      (P.a * (-2 + P.γ) + P.c * (2 - P.c * P.γ)))

end
end QuantumEcon.Duopoly


