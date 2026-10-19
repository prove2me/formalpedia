-- Prove2me | Definitions.Def_NonExclEncroach_Channels_Model
-- name    : NonExclEncroach_Channels_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:52.650286+00:00
-- url     : https://prove2.me/theorems/ed87b5b3-ccca-49f1-b189-16f83bbf9bd0
-- title:
--   §3–§4, pp. 5–18 — two suppliers, a non-exclusive reseller and supplier 1's direct channel (θ1d = 1): demand, payoffs, belief-based equilibrium, thresholds c0–c3
-- statement:
--   This file sets up the supplier-encroachment game of Hotkar and Gilbert in the case where supplier 1's direct channel is a perfect substitute for the reselling channel ($\theta_{1d}=1$, hence $\theta_{2d}=\theta_{12}$).
--
--   **Demand and payoffs.** Write $\theta=\theta_{12}\in(0,1)$ for the substitutability between the two suppliers' products. The reseller orders $q_1$ from supplier 1 and $q_2$ from supplier 2, and supplier 1 sells $y$ units directly. The market-clearing prices (3.1)–(3.3) are
--   $$p_1=1-q_1-\theta q_2-y,\qquad p_2=1-q_2-\theta q_1-\theta y,\qquad p_d=1-y-q_1-\theta q_2 .$$
--   With wholesale prices $w_1,w_2$ and a per-unit direct selling cost $c$ (which may be negative), the reseller earns $\pi=q_1(p_1-w_1)+q_2(p_2-w_2)$, supplier 1 earns $\Pi_1=y(p_d-c)+q_1w_1$, and supplier 2 earns $\Pi_2=q_2w_2$, as in (3.4)–(3.6).
--
--   **Timing and information.** In stage I the suppliers set $w_1,w_2$ simultaneously; neither observes the rival's price. In stage II the reseller orders $(q_1,q_2)$. In stage III supplier 1 observes $q_1$ only and chooses $y$. Supplier 1 holds a belief $w_2'$ about $w_2$.
--
--   **Stage III** (4.12)–(4.16). Given $q_1$ and her belief $w_2'$, supplier 1's direct quantity $y$ and her conjecture $q_2'$ of the reseller's order from supplier 2 are mutual best responses: $y$ maximizes $z(p_d-c)$ over $z\ge0$ against $q_2'$, and $q_2'$ maximizes the reseller's profit over $q_2\ge0$ against $y$ when supplier 2's price is $w_2'$.
--
--   **Strategy profiles and equilibrium.** A profile consists of the prices $w_1,w_2$, supplier 1's rules $q_1\mapsto y$ and $q_1\mapsto q_2'$ (computed with her belief $w_2'=w_2$), and the reseller's order rule $(w_1,w_2)\mapsto(q_1,q_2)$ at every pair of non-negative prices. It is an **equilibrium** in the sense of (4.7)–(4.11) when
--   1. supplier 1's rules solve stage III at every observed $q_1\ge0$;
--   2. at every price pair the reseller's order maximizes $\pi$ over $q_1,q_2\ge0$, anticipating supplier 1's response $y(q_1)$;
--   3. no price $w_1\ge0$ gives supplier 1 a higher $\Pi_1$, her belief about $w_2$ being unchanged;
--   4. no price $w_2\ge0$ gives supplier 2 a higher $\Pi_2$; the deviation changes the price the reseller faces but not supplier 1's belief.
--
--   The equilibrium quantities are $q_1^*,q_2^*$ (the reseller's order at the equilibrium prices) and $y^*=y(q_1^*)$.
--
--   **Closed forms.** The file also defines the paper's thresholds and prices: $c_0,c_1,c_2,c_3$ (Table 2), $\mathrm{Num1}(\theta)$ (proof of Proposition 5), the standing range $0<\theta<1$, $c_0<c<c_3$ (p. 9), the threshold $\bar q_1(w_2')$ and the branches (4.17)–(4.19) of Lemmas 1–2, $\bar w(w_2,w_2')$, and the prices $w_2^{DO}$, $w_1^{DOB}$, $w_2^{DOB}$, $w_1^{R\&D}$, $w_2^{R\&D}$ of Table 1 / Table 2.
--
--   This is the common model of every statement of the mission.
--
--   **Formalization Note** Everything is real-valued. Prices and quantities range over $[0,\infty)$, as in Lemma 3 ("for any non-negative wholesale prices"). Beliefs are not separate fields: in equilibrium they equal the actual prices (4.11), and off the path only supplier 1's belief matters, which stays at the equilibrium $w_2$. Best responses are argmaxes without a tie-breaking rule. Stage II maximizes jointly over $(q_1,q_2)$, which equals (4.7)–(4.8) because supplier 1's response depends on $q_1$ only (the reordering-invariance reading of p. 14). §5 ($\theta_{1d}=0.8$) is out of scope.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, pp. 5–18 (PDF 5–18), §3, §4, (3.1)–(3.6), (4.7)–(4.19), Table 1, Table 2 p. 33 (PDF 33); Online Technical Appendix p. 6 (PDF 39) and p. 16 (PDF 49)

import Mathlib

namespace NonExclEncroach.Channels

noncomputable section

/-! Hotkar & Gilbert, *Supplier Encroachment in a Non-Exclusive Reselling Channel*,
SSRN working paper 3238502, §3–§4. The case formalized is `θ1d = 1` (§4, p. 11), hence
`θ2d = θ12 · θ1d = θ12`; `θ` stands for `θ12` throughout. Wholesale prices and quantities
range over `[0, ∞)`. -/

/-- Market-clearing price of supplier 1's product in the reselling channel, (3.1) at `θ1d = 1`. -/
def p1 (θ q1 q2 y : ℝ) : ℝ := 1 - q1 - θ * q2 - y

/-- Market-clearing price of supplier 2's product, (3.2) at `θ2d = θ`. -/
def p2 (θ q1 q2 y : ℝ) : ℝ := 1 - q2 - θ * q1 - θ * y

/-- Market-clearing price in supplier 1's direct channel, (3.3) at `θ1d = 1`, `θ2d = θ`. -/
def pd (θ q1 q2 y : ℝ) : ℝ := 1 - y - q1 - θ * q2

/-- The reseller's profit `π(q1, q2, w1, w2, y)`, (3.4). -/
def resellerProfit (θ q1 q2 w1 w2 y : ℝ) : ℝ :=
  q1 * (p1 θ q1 q2 y - w1) + q2 * (p2 θ q1 q2 y - w2)

/-- Supplier 1's profit `Π1(q1, q2, w1, y)`, (3.5). -/
def supplier1Profit (θ c q1 q2 w1 y : ℝ) : ℝ := y * (pd θ q1 q2 y - c) + q1 * w1

/-- Supplier 2's profit `Π2(q2, w2)`, (3.6). -/
def supplier2Profit (q2 w2 : ℝ) : ℝ := q2 * w2

/-- The lower bound `c0` on the direct cost (p. 9; Table 2, p. 33). -/
def c0 (θ : ℝ) : ℝ := -((2 - θ) * (8 - θ ^ 2 - θ ^ 3)) / (2 * (8 - 5 * θ ^ 2))

/-- The threshold `c1` (Table 2, p. 33). -/
def c1 (θ : ℝ) : ℝ := (4 * θ - 14 * θ ^ 2 + 5 * θ ^ 3 - θ ^ 4) / (32 - 26 * θ ^ 2)

/-- The threshold `c2` (Table 2, p. 33; (A.5)). -/
def c2 (θ : ℝ) : ℝ :=
  (32 * θ - 80 * θ ^ 2 - 32 * θ ^ 3 - 14 * θ ^ 4 - 8 * θ ^ 5 + 4 * θ ^ 6 - θ ^ 7) /
    (2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4))

/-- The upper bound `c3` on the direct cost (p. 9; Table 2, p. 33; (A.6)). -/
def c3 (θ : ℝ) : ℝ :=
  (384 - 64 * θ + 8 * θ ^ 2 - 24 * θ ^ 3 - 60 * θ ^ 4 + 6 * θ ^ 5 - 9 * θ ^ 6 + θ ^ 7 + θ ^ 8) /
    (2 * (320 - 36 * θ ^ 2 - 42 * θ ^ 4 + θ ^ 6))

/-- `Num1(θ12)`, the numerator of `c2` up to the factor `θ12` (proof of Proposition 5,
Online Technical Appendix p. 16). -/
def num1 (θ : ℝ) : ℝ := 32 - θ * (80 + θ * (32 + θ * (14 + θ * (8 - (4 - θ) * θ))))

/-- The standing assumptions of §3–§4: `θ12 ∈ (0, 1)` and `c0 < c < c3` (p. 9). -/
def Standing (θ c : ℝ) : Prop := 0 < θ ∧ θ < 1 ∧ c0 θ < c ∧ c < c3 θ

/-- The threshold `q̄1(w′2)` of Lemma 1 (p. 15; Table 2). -/
def qbar1 (θ c b : ℝ) : ℝ := (2 * (1 - c) - θ * (1 - b)) / (2 * (1 - θ ^ 2))

/-- Supplier 1's direct quantity `y^III(w′2, q1)`, (4.17). -/
def yIII (θ c b q1 : ℝ) : ℝ :=
  if q1 ≤ qbar1 θ c b then
    (2 * (1 - c) - θ * (1 - b)) / (4 - θ ^ 2) - 2 * (1 - θ ^ 2) / (4 - θ ^ 2) * q1
  else 0

/-- The upper branch of (4.18). -/
def q2conjUpper (θ c b q1 : ℝ) : ℝ :=
  (2 * (1 - b) - θ * (1 - c)) / (4 - θ ^ 2) - 3 * θ / (4 - θ ^ 2) * q1

/-- Supplier 1's rational conjecture `q′2(w′2, q1)`, (4.18). -/
def q2conj (θ c b q1 : ℝ) : ℝ :=
  if q1 ≤ qbar1 θ c b then q2conjUpper θ c b q1 else max ((1 - 2 * θ * q1 - b) / 2) 0

/-- The upper branch of (4.19). -/
def q2IIIUpper (θ c w2 b q1 : ℝ) : ℝ :=
  (2 * (1 - w2) - θ * (1 - c) - 3 * θ * q1) / (4 - θ ^ 2) - θ ^ 2 * (b - w2) / (2 * (4 - θ ^ 2))

/-- The reseller's conditionally optimal order from supplier 2, `q2^III(w2, w′2, q1)`, (4.19). -/
def q2III (θ c w2 b q1 : ℝ) : ℝ :=
  if q1 ≤ qbar1 θ c b then q2IIIUpper θ c w2 b q1 else max ((1 - 2 * θ * q1 - w2) / 2) 0

/-- `w̄(w2, w′2)` (Table 2; Online Technical Appendix p. 6). -/
def wU (θ c w2 b : ℝ) : ℝ :=
  ((1 - θ) * (8 - θ ^ 3 + 8 * (1 + θ) * c) + 3 * θ * (4 - θ ^ 2) * w2
      - 4 * θ * (1 - θ ^ 2) * b) / (4 - θ ^ 2) ^ 2

/-- `w2^DO` (Table 1, p. 18; Table 2). -/
def wDO2 (θ c : ℝ) : ℝ := 2 * (2 - θ * (1 - c)) / (8 - θ ^ 2)

/-- `w1^DOB` (Table 1, p. 18; Table 2). -/
def wDOB1 (θ c : ℝ) : ℝ :=
  4 * (1 - θ ^ 2) * (2 + θ ^ 2 - 6 * c) / ((4 - θ ^ 2) * (4 + 5 * θ ^ 2))

/-- `w2^DOB` (Table 1, p. 18; Table 2). -/
def wDOB2 (θ c : ℝ) : ℝ :=
  (1 - θ) * (4 * θ - 4 * θ ^ 2 + θ ^ 3 - 16 * c * (1 + θ)) / (θ * (4 + 5 * θ ^ 2))

/-- `w1^{R&D}` (Table 2, p. 33). -/
def wRD1 (θ c : ℝ) : ℝ :=
  (128 * (3 - c) - θ * (128 + θ * (56 + θ * (96 + θ * (90 - 5 * θ ^ 4 + θ ^ 3
      + 34 * θ ^ 2 * c + 18 * θ + 6 * c)) - 168 * c))) /
    (3 * (256 + 2 * θ ^ 8 - 11 * θ ^ 6 - 52 * θ ^ 4 + 48 * θ ^ 2))

/-- `w2^{R&D}` (Table 2, p. 33). -/
def wRD2 (θ c : ℝ) : ℝ :=
  (1 - θ) * (8 + θ ^ 2) * (16 + θ * (8 - 3 * θ ^ 3 - 4 * (1 + θ) * (2 - θ ^ 2) * c + 4 * θ)) /
    (256 + 2 * θ ^ 8 - 11 * θ ^ 6 - 52 * θ ^ 4 + 48 * θ ^ 2)

/-- `x` maximizes `f` over `[0, ∞)`. -/
def IsBestResponse (f : ℝ → ℝ) (x : ℝ) : Prop := 0 ≤ x ∧ ∀ z, 0 ≤ z → f z ≤ f x

/-- Stage III under supplier 1's belief `b = w′2` about supplier 2's price, after observing `q1`:
her direct quantity `y` and her conjecture `q2'` of the reseller's order from supplier 2 are
mutual best responses, (4.12)–(4.16). The reseller's objective uses the believed price `b`;
its `w1` argument is `0` because `w1` enters (3.4) only through `−q1·w1`, constant in `q2`. -/
def IsStageIII (θ c b q1 y q2' : ℝ) : Prop :=
  IsBestResponse (fun z => z * (pd θ q1 q2' z - c)) y ∧
  IsBestResponse (fun z => resellerProfit θ q1 z 0 b y) q2'

/-- A strategy profile in which both suppliers' beliefs equal the actual prices (4.11):
the wholesale prices, supplier 1's direct-quantity rule `Y` and conjecture rule `Q2c`
(both functions of the observed `q1`, computed with her belief `w′2 = w2`), and the reseller's
order rule `R` at every pair of wholesale prices. -/
structure Profile where
  w1 : ℝ
  w2 : ℝ
  Y : ℝ → ℝ
  Q2c : ℝ → ℝ
  R : ℝ → ℝ → ℝ × ℝ

/-- The equilibrium (4.7)–(4.16) with consistent beliefs (4.11). Supplier 1's belief about
supplier 2's price stays `σ.w2` after any deviation; supplier 2's deviation changes the actual
price the reseller faces but not supplier 1's belief. -/
def IsEquilibrium (θ c : ℝ) (σ : Profile) : Prop :=
  0 ≤ σ.w1 ∧ 0 ≤ σ.w2 ∧
  (∀ q1, 0 ≤ q1 → IsStageIII θ c σ.w2 q1 (σ.Y q1) (σ.Q2c q1)) ∧
  (∀ w1 w2, 0 ≤ w1 → 0 ≤ w2 →
    0 ≤ (σ.R w1 w2).1 ∧ 0 ≤ (σ.R w1 w2).2 ∧
    ∀ q1 q2, 0 ≤ q1 → 0 ≤ q2 →
      resellerProfit θ q1 q2 w1 w2 (σ.Y q1) ≤
        resellerProfit θ (σ.R w1 w2).1 (σ.R w1 w2).2 w1 w2 (σ.Y (σ.R w1 w2).1)) ∧
  (∀ w1, 0 ≤ w1 →
    supplier1Profit θ c (σ.R w1 σ.w2).1 (σ.R w1 σ.w2).2 w1 (σ.Y (σ.R w1 σ.w2).1) ≤
      supplier1Profit θ c (σ.R σ.w1 σ.w2).1 (σ.R σ.w1 σ.w2).2 σ.w1 (σ.Y (σ.R σ.w1 σ.w2).1)) ∧
  (∀ w2, 0 ≤ w2 →
    supplier2Profit (σ.R σ.w1 w2).2 w2 ≤ supplier2Profit (σ.R σ.w1 σ.w2).2 σ.w2)

/-- Equilibrium order quantity from supplier 1, `q1*`. -/
def Profile.q1 (σ : Profile) : ℝ := (σ.R σ.w1 σ.w2).1

/-- Equilibrium order quantity from supplier 2, `q2*`. -/
def Profile.q2 (σ : Profile) : ℝ := (σ.R σ.w1 σ.w2).2

/-- Equilibrium direct-channel quantity of supplier 1, `y*`. -/
def Profile.y (σ : Profile) : ℝ := σ.Y σ.q1

end

end NonExclEncroach.Channels


