-- Prove2me | Definitions.Def_CyberShare_Sharing_Model
-- name    : CyberShare_Sharing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:57:54.50753+00:00
-- url     : https://prove2.me/theorems/147e7cd0-4ea0-4ade-a237-38e094be643a
-- title:
--   §3 and Definition 1 — attack shocks, signals, investments, prices, and sharing equilibrium
-- statement:
--   Two firms sell imperfect substitutes. Firm $i$ charges $p_i$ and faces demand $D_i=a-p_i+bp_j$, where $b\in[0,1]$. An attack raises its marginal cost from $c$ to $c+(\delta-\gamma K_i)^+$ after resilience investment $K_i\ge0$, where $x^+=\max\{x,0\}$. Its profit is
--
--   $$
--   \pi_i=(p_i-c-\alpha_i(\delta-\gamma K_i)^+)(a-p_i+bp_j)-\kappa K_i^2.
--   $$
--
--   The common state has attack likelihood $\theta_L$ with probability $1-\rho$ and $\theta_H$ with probability $\rho$. Conditional on that state, the firms' attacks are independent. Each firm sees a private low or high signal that reports the state correctly with probability $\lambda$; signals are conditionally independent. A firm that shares its signal lets the other firm condition its investment on both signals. The model uses the paper's three stages: sharing, investment, and pricing after attacks are observed.
--
--   A price equilibrium maximizes each firm's realized profit over prices at least its realized marginal cost. An investment equilibrium selects a nonnegative investment for every available information cell and maximizes the conditional expected true profit at the price rule of Lemma 1. A sharing equilibrium requires investment equilibria both on path and after either unilateral sharing deviation, and compares ex-ante profits after each subgame re-equilibrates. All investment-equilibrium selections enter that comparison.
--
--   **Formalization Note** The outcome law and expectations use finite sums over 32 outcomes. Conditional sums are unnormalised, which leaves the argmax unchanged because each information cell has positive probability under the standing assumptions. Lemma 1 separately establishes that the price rule is the unique price equilibrium. The printed formula (C.12) defines $\underline\delta$ as a sufficient interiority bound. The strict condition $\theta_L<\theta_H$, interior prior $0<\rho<1$, and nonnegative marginal cost $c\ge0$ are disclosed additions to the paper's standing conditions.
-- source:
--   August, Noh, Shamir & Shin, Cyberattacks, Operational Disruption and Investment in Resilience Measures, SSRN 4032257 (version of 2022-02-10), pp. 8–11 (PDF 9–12), §3–§4, (1)–(8); p. A.2 (PDF 34), Definition 1; p. A.8 (PDF 40), (C.12); https://ssrn.com/abstract=4032257

import Mathlib

noncomputable section

namespace CyberShare.Sharing

inductive Sig | L | H deriving DecidableEq
inductive Dec | S | N deriving DecidableEq

instance : Fintype Sig := ⟨{.L, .H}, by intro x; cases x <;> simp⟩
instance : Fintype Dec := ⟨{.S, .N}, by intro x; cases x <;> simp⟩

/-- Parameters of the two-firm model in Section 3. -/
structure Params where
  a : ℝ
  b : ℝ
  c : ℝ
  delta : ℝ
  gamma : ℝ
  kappa : ℝ
  thL : ℝ
  thH : ℝ
  rho : ℝ
  lam : ℝ

/-- The hypotheses common to Proposition 2 before competition, investment cost and impact are chosen. -/
def BaseStanding (a c gamma thL thH rho lam : ℝ) : Prop :=
  0 ≤ c ∧ 0 < gamma ∧ 0 < thL ∧ thL < thH ∧ thH ≤ 1 ∧
  1 - thH < thL ∧ 0 < rho ∧ rho < 1 ∧
  (1 / 2 : ℝ) < lam ∧ lam < 1 ∧ c < a

/-- Section 3's domain, including the disclosed strict signal distinction, interior prior and
nonnegative marginal cost. -/
def Params.Standing (P : Params) : Prop :=
  BaseStanding P.a P.c P.gamma P.thL P.thH P.rho P.lam ∧
  0 ≤ P.b ∧ P.b ≤ 1 ∧ 0 < P.delta ∧ P.c + P.delta < P.a ∧ 0 < P.kappa

/-- The state, two private signals and two subsequent attack indicators. -/
structure Outcome where
  st : Sig
  y1 : Sig
  y2 : Sig
  attack1 : Bool
  attack2 : Bool
  deriving DecidableEq, Fintype

def stateValue (P : Params) : Sig → ℝ
  | .L => P.thL
  | .H => P.thH

def prior (P : Params) : Sig → ℝ
  | .L => 1 - P.rho
  | .H => P.rho

/-- Conditional probability of a signal given the state, equation (5). -/
def signalProb (P : Params) (st y : Sig) : ℝ :=
  if st = y then P.lam else 1 - P.lam

def attackProb (P : Params) (st : Sig) (attacked : Bool) : ℝ :=
  if attacked then stateValue P st else 1 - stateValue P st

/-- Probability of one of the 32 outcomes. Conditional independence is encoded by the product. -/
def prob (P : Params) (w : Outcome) : ℝ :=
  prior P w.st * signalProb P w.st w.y1 * signalProb P w.st w.y2 *
    attackProb P w.st w.attack1 * attackProb P w.st w.attack2

def pos (x : ℝ) : ℝ := max x 0

def cost (P : Params) (attack : Bool) (K : ℝ) : ℝ :=
  P.c + (if attack then pos (P.delta - P.gamma * K) else 0)

/-- Equation (4): true profit, including the positive part of the disruption cost. -/
def profit (P : Params) (attack : Bool) (K p pOther : ℝ) : ℝ :=
  (p - cost P attack K) * (P.a - p + P.b * pOther) - P.kappa * K ^ 2

/-- Equation (7) and Definition 1(a): each price maximizes profit above its own realized cost. -/
def IsPriceEq (P : Params) (attack1 attack2 : Bool)
    (K1 K2 p1 p2 : ℝ) : Prop :=
  cost P attack1 K1 ≤ p1 ∧ cost P attack2 K2 ≤ p2 ∧
  (∀ x : ℝ, cost P attack1 K1 ≤ x →
    profit P attack1 K1 x p2 ≤ profit P attack1 K1 p1 p2) ∧
  (∀ x : ℝ, cost P attack2 K2 ≤ x →
    profit P attack2 K2 x p1 ≤ profit P attack2 K2 p2 p1)

/-- Lemma 1's price rule. Its equivalence to `IsPriceEq` is a separate theorem. -/
def pStar (P : Params) (attackOwn attackOther : Bool) (KOwn KOther : ℝ) : ℝ :=
  (P.a + P.c) / (2 - P.b) +
  (if attackOwn then 2 * pos (P.delta - P.gamma * KOwn) / (4 - P.b ^ 2) else 0) +
  (if attackOther then P.b * pos (P.delta - P.gamma * KOther) / (4 - P.b ^ 2) else 0)

/-- A firm observes its own signal and the rival's signal only when the rival shares. -/
def Adapted (other : Dec) (K : Sig → Sig → ℝ) : Prop :=
  other = .N → ∀ y y' y'', K y y' = K y y''

def cell1 (other : Dec) (yOwn yOther : Sig) : Finset Outcome :=
  Finset.univ.filter (fun w => w.y1 = yOwn ∧ (other = .N ∨ w.y2 = yOther))

def cell2 (other : Dec) (yOwn yOther : Sig) : Finset Outcome :=
  Finset.univ.filter (fun w => w.y2 = yOwn ∧ (other = .N ∨ w.y1 = yOther))

/-- A deviation changes precisely one information cell of firm 1's strategy. -/
def dev1 (other : Dec) (K : Sig → Sig → ℝ) (yOwn yOther : Sig) (x : ℝ) :
    Sig → Sig → ℝ :=
  fun z z' => if z = yOwn ∧ (other = .N ∨ z' = yOther) then x else K z z'

/-- A deviation changes precisely one information cell of firm 2's strategy. -/
def dev2 (other : Dec) (K : Sig → Sig → ℝ) (yOwn yOther : Sig) (x : ℝ) :
    Sig → Sig → ℝ :=
  fun z z' => if z = yOwn ∧ (other = .N ∨ z' = yOther) then x else K z z'

/-- Firm 1's realized profit at Lemma 1's price rule. -/
def payoff1 (P : Params) (K1 K2 : Sig → Sig → ℝ) (w : Outcome) : ℝ :=
  let k1 := K1 w.y1 w.y2
  let k2 := K2 w.y2 w.y1
  profit P w.attack1 k1 (pStar P w.attack1 w.attack2 k1 k2)
    (pStar P w.attack2 w.attack1 k2 k1)

/-- Firm 2's realized profit at Lemma 1's price rule. -/
def payoff2 (P : Params) (K1 K2 : Sig → Sig → ℝ) (w : Outcome) : ℝ :=
  let k1 := K1 w.y1 w.y2
  let k2 := K2 w.y2 w.y1
  profit P w.attack2 k2 (pStar P w.attack2 w.attack1 k2 k1)
    (pStar P w.attack1 w.attack2 k1 k2)

/-- Definition 1(b): nonnegative, information-adapted investments maximize the true conditional
profit. The finite sums are unnormalised conditional expectations; every information cell has
positive probability under `Standing`. The price stage uses Lemma 1's rule. -/
def IsInvEq (P : Params) (s1 s2 : Dec) (K1 K2 : Sig → Sig → ℝ) : Prop :=
  Adapted s2 K1 ∧ Adapted s1 K2 ∧
  (∀ y y', 0 ≤ K1 y y' ∧ 0 ≤ K2 y y') ∧
  (∀ y y' x, 0 ≤ x →
    (∑ w ∈ cell1 s2 y y', prob P w * payoff1 P (dev1 s2 K1 y y' x) K2 w) ≤
    (∑ w ∈ cell1 s2 y y', prob P w * payoff1 P K1 K2 w)) ∧
  (∀ y y' x, 0 ≤ x →
    (∑ w ∈ cell2 s1 y y', prob P w * payoff2 P K1 (dev2 s1 K2 y y' x) w) ≤
    (∑ w ∈ cell2 s1 y y', prob P w * payoff2 P K1 K2 w))

def exAnte1 (P : Params) (K1 K2 : Sig → Sig → ℝ) : ℝ :=
  ∑ w : Outcome, prob P w * payoff1 P K1 K2 w

def exAnte2 (P : Params) (K1 K2 : Sig → Sig → ℝ) : ℝ :=
  ∑ w : Outcome, prob P w * payoff2 P K1 K2 w

def flip : Dec → Dec
  | .S => .N
  | .N => .S

/-- Definition 1(c): an investment equilibrium exists on and off path, and neither firm benefits
from a sharing deviation when the deviation subgame re-equilibrates. The inequalities hold for
every investment equilibrium selection. -/
def IsSharingEq (P : Params) (s1 s2 : Dec) : Prop :=
  (∃ K1 K2, IsInvEq P s1 s2 K1 K2) ∧
  (∃ K1 K2, IsInvEq P (flip s1) s2 K1 K2) ∧
  (∃ K1 K2, IsInvEq P s1 (flip s2) K1 K2) ∧
  (∀ K1 K2 K1' K2', IsInvEq P s1 s2 K1 K2 →
    IsInvEq P (flip s1) s2 K1' K2' →
    exAnte1 P K1' K2' ≤ exAnte1 P K1 K2) ∧
  (∀ K1 K2 K1' K2', IsInvEq P s1 s2 K1 K2 →
    IsInvEq P s1 (flip s2) K1' K2' →
    exAnte2 P K1' K2' ≤ exAnte2 P K1 K2)

/-- The printed formula (C.12), used as a sufficient interiority bound. -/
def deltaLow (P : Params) : ℝ :=
  P.gamma ^ 2 * (P.a + (P.b - 1) * P.c) *
  (((-P.b ^ 2 + P.thL * P.b + 2) * P.thL * (1 - P.lam) ^ 2 * (1 - P.rho)) +
   ((-P.b ^ 2 + P.thH * P.b + 2) * P.thH * P.lam ^ 2 * P.rho)) /
  ((2 - P.b) ^ 2 * (P.b + 2) * ((2 * P.lam - 1) * P.rho + (1 - P.lam) ^ 2)) /
  P.kappa

end CyberShare.Sharing


