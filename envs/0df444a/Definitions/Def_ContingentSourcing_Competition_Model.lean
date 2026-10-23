-- Prove2me | Definitions.Def_ContingentSourcing_Competition_Model
-- name    : ContingentSourcing_Competition_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:58.989235+00:00
-- url     : https://prove2.me/theorems/0a6f3e90-c395-4be7-8dc6-0c0213bc241d
-- title:
--   §3–§4.3, pp. 8–19 — buyer's two-stage sourcing program (2), Table 1 orders, supplier payoffs (5)–(6), Pareto-dominant Nash equilibrium, thresholds ψ, ϕ
-- statement:
--   This file sets up the contingent-sourcing model of Lu and Tomlin (§3, pp. 8–12) and the supplier pricing game of §4 (pp. 13–19).
--
--   **Parameters.** A buyer sells at the price $p(q)=m-q$, where $m>0$ is the market potential. For an available quantity $Q$ the revenue is
--   $$R(Q)=\begin{cases} mQ-Q^2 & Q\le m/2,\\ m^2/4 & \text{otherwise}\end{cases}\qquad(1).$$
--   Supplier U is unreliable: its shipment arrives with probability $P_1\in(0,1)$ and is spoiled with probability $P_0=1-P_1$; its unit cost is $c_U$. Supplier R is reliable with unit cost $c_R$. The standing assumptions are $0<m$, $0<P_1<1$, $0\le c_U\le P_1m$ and $0\le c_R\le m$.
--
--   **Information.** At Time 1 the buyer sees a signal $s\in\{B,G\}$ of accuracy $\rho\in[0,1]$: a spoiled shipment gives $s=B$ with probability $\rho$, an intact one always gives $s=G$. Hence $P_B=P_0\rho$, $P_G=1-P_0\rho$, and the posteriors are $P_{1G}=1-P_{0G}=P_1/(P_1+P_0(1-\rho))$, $P_{0B}=1$, $P_{1B}=0$.
--
--   **The buyer's problem (2).** Given prices $w_U$ (supplier U), $w_R$ (supplier R, regular, Time 0) and $w_E$ (supplier R, emergency, Time 1), the buyer chooses $Q_U,Q_R\ge0$ at Time 0 and $Q_E(G),Q_E(B)\ge 0$ at Time 1 to maximize
--   $$\sum_{s\in\{B,G\}}P_s\sum_{\epsilon\in\{0,1\}}P_{\epsilon s}\big[R(\epsilon Q_U+Q_R+Q_E(s))-w_EQ_E(s)-w_RQ_R-w_U\epsilon Q_U\big].$$
--   U is paid only on delivery. The buyer's value is the supremum of this objective over feasible orders.
--
--   **Table 1 (p. 13).** With $\eta_1(w_U,w_E)=P_1w_U+P_Bw_E+P_GP_{0G}m$ and $\eta_2(w_U,w_E)=P_1w_U+P_0w_E$, the four candidate orders (with $Q_E(G)=0$, and $Q_E$ meaning $Q_E(B)$) are
--
--   | case | $Q_U$ | $Q_R$ | $Q_E$ |
--   |---|---|---|---|
--   | i (contingent) | $(m-w_U)/2$ | $0$ | $(m-w_E)/2$ |
--   | ii (mixed) | $\frac{w_R-P_Gw_U-P_Bw_E}{2P_GP_{0G}}$ | $\frac{P_GP_{0G}m-w_R+P_Bw_E+P_1w_U}{2P_GP_{0G}}$ | $\frac{w_R-P_1w_U-P_0w_E}{2P_GP_{0G}}$ |
--   | iii (diversification) | $\frac{w_R-w_U}{2P_0}$ | $\frac{P_0m-w_R+P_1w_U}{2P_0}$ | $0$ |
--   | iv (sole) | $0$ | $(m-w_R)/2$ | $0$ |
--
--   The buyer's response used in the game takes case iv if $w_R\le w_U$, else case i if $\eta_1\le w_R$, else case ii if $\eta_2<w_R$, else case iii.
--
--   **The pricing game.** Supplier R's payoff (5) is $\pi_R=(w_R-c_R)Q_R+P_B(w_E-c_R)Q_E$ and supplier U's payoff (6) is $\pi_U=(P_1w_U-c_U)Q_U$, at the buyer's response. Strategy spaces are $c_U/P_1\le w_U\le m$ for U and $c_R\le w_R\le w_E\le m$ for R (p. 16). A Nash equilibrium is a profile in which $(w_R,w_E)$ maximizes $\pi_R$ given $w_U$ and $w_U$ maximizes $\pi_U$ given $(w_R,w_E)$. An *equilibrium* is a Pareto-dominant Nash equilibrium: no other Nash equilibrium gives both suppliers at least as much and one of them strictly more. A best response of R to $w_U$ is a feasible $(w_R,w_E)$ maximizing $\pi_R$.
--
--   **Thresholds.** $\psi_1=\frac{P_1m+c_U}{2P_1}$, $\psi_2=\frac{P_0m+2c_U/P_1}{P_0+2}$, $\psi_3=\frac{P_0+1}{P_1}c_U-P_0m$ (p. 16), $\phi_1=\frac{(1+P_0)m+c_U}{2}$, $\phi_2=\frac{2P_0m+c_U}{P_0+1}$ (p. 18), and the buyer threshold $m-\frac{P_1m-c_U}{\sqrt{4-P_1+P_1^2}}$ of Proposition 4. The file also records the price profiles of Table 2 (i-a)/(i-b) at $\rho=1$ (with $w_R$ at the lower end $P_1w_U+P_0w_E$ of the (i-a) interval) and of Table 3 (i-a), (i-b), (ii) at $\rho=0$ (with $w_R=c_R$ in case (i) and $w_E=m$, which is irrelevant at $\rho=0$), and the predicate "the buyer is in the contingent case".
--
--   These objects are shared by every statement of the mission: Proposition 1 and Lemma 1 describe the buyer's response, Lemma A.1 and Propositions 2–3 the equilibria at $\rho=1$ and $\rho=0$, and Proposition 4 compares them.
--
--   **Formalization Note.** $\rho$ is an argument, not a parameter; Scenario I is $\rho=1$ and Scenario N is $\rho=0$. The objective (2) is written as printed, with $P_{0B}=1$, $P_{1B}=0$ substituted. The buyer's value is a supremum (`sSup`) over feasible orders; it is meaningful when the objective is bounded above, which holds for nonnegative prices (in particular at every equilibrium). The case order of the buyer's response carries footnote 11's tie-break: at $\eta_1=w_R$ the buyer sources contingently; for $\rho<1$ the Table 1 quantities agree on the case boundaries, so only $\rho=1$ is affected. Case ii divides by $2P_GP_{0G}$, which is $0$ at $\rho=1$, where case ii is empty. The nonnegativity of $m$, $c_U$, $c_R$ is implicit in the paper and made explicit. Pareto dominance is read as weak dominance (at least as much for both, strictly more for one), as in the proof of Proposition 2.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, pp. 8–19 (PDF 8–19), §3, §4.1–4.3, eqs. (1)–(6), Table 1, footnote 11, strategy spaces and equilibrium selection p. 16, thresholds pp. 16, 18, Tables 2–3 pp. 17, 19; Proposition 4 p. 22

import Mathlib

namespace ContingentSourcing.Competition

/-- Parameters, §3 (pp. 8–12): market potential m (price m − q), U's delivery probability P1,
unit costs cU (supplier U) and cR (supplier R). The signal accuracy ρ is an argument, not a parameter. -/
structure Params where
  m : ℝ
  P1 : ℝ
  cU : ℝ
  cR : ℝ

/-- Standing assumptions: 0 < P1 < 1 (p. 8), cU ≤ P1 m and cR ≤ m (p. 12); 0 < m, 0 ≤ cU, 0 ≤ cR implicit. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.m ∧ 0 < P.P1 ∧ P.P1 < 1 ∧ 0 ≤ P.cU ∧ P.cU ≤ P.P1 * P.m ∧ 0 ≤ P.cR ∧ P.cR ≤ P.m

def Params.P0 (P : Params) : ℝ := 1 - P.P1
/-- Signal probabilities and posteriors (p. 11): PB = P0 ρ, PG = 1 − P0 ρ, P0G = Pr(ε = 0 | G),
P1G = Pr(ε = 1 | G); P0B = 1 and P1B = 0 are used directly in `buyerProfit`. -/
def Params.PB (P : Params) (ρ : ℝ) : ℝ := P.P0 * ρ
def Params.PG (P : Params) (ρ : ℝ) : ℝ := 1 - P.P0 * ρ
noncomputable def Params.P0G (P : Params) (ρ : ℝ) : ℝ := P.P0 * (1 - ρ) / P.PG ρ
noncomputable def Params.P1G (P : Params) (ρ : ℝ) : ℝ := P.P1 / P.PG ρ

/-- Revenue (1), p. 8: R(Q) = mQ − Q² if Q ≤ m/2, m²/4 otherwise. -/
noncomputable def Params.revenue (P : Params) (Q : ℝ) : ℝ :=
  if Q ≤ P.m / 2 then P.m * Q - Q ^ 2 else P.m ^ 2 / 4

/-- Wholesale prices: U's wU, R's regular wR and emergency wE (p. 10). -/
structure Prices where
  wU : ℝ
  wR : ℝ
  wE : ℝ

/-- Order quantities: initial QU, QR (Time 0) and emergency QE(G), QE(B) (Time 1). -/
structure Orders where
  QU : ℝ
  QR : ℝ
  QEG : ℝ
  QEB : ℝ

def Orders.Feasible (q : Orders) : Prop := 0 ≤ q.QU ∧ 0 ≤ q.QR ∧ 0 ≤ q.QEG ∧ 0 ≤ q.QEB

/-- The buyer's expected profit, the objective of (2), p. 11, with P0B = 1, P1B = 0. -/
noncomputable def Params.buyerProfit (P : Params) (ρ : ℝ) (w : Prices) (q : Orders) : ℝ :=
  P.PB ρ * (P.revenue (q.QR + q.QEB) - w.wE * q.QEB - w.wR * q.QR)
  + P.PG ρ * (P.P0G ρ * (P.revenue (q.QR + q.QEG) - w.wE * q.QEG - w.wR * q.QR)
      + P.P1G ρ * (P.revenue (q.QU + q.QR + q.QEG) - w.wE * q.QEG - w.wR * q.QR - w.wU * q.QU))

def Params.IsOptimalOrder (P : Params) (ρ : ℝ) (w : Prices) (q : Orders) : Prop :=
  q.Feasible ∧ ∀ q' : Orders, q'.Feasible → P.buyerProfit ρ w q' ≤ P.buyerProfit ρ w q

/-- The buyer's optimal expected profit: the supremum of (2) over feasible orders. -/
noncomputable def Params.buyerValue (P : Params) (ρ : ℝ) (w : Prices) : ℝ :=
  sSup {v | ∃ q : Orders, q.Feasible ∧ v = P.buyerProfit ρ w q}

/-- η1(wU, wE) = P1 wU + PB wE + PG P0G m and η2(wU, wE) = P1 wU + P0 wE, p. 13. -/
noncomputable def Params.eta1 (P : Params) (ρ : ℝ) (w : Prices) : ℝ :=
  P.P1 * w.wU + P.PB ρ * w.wE + P.PG ρ * P.P0G ρ * P.m
def Params.eta2 (P : Params) (w : Prices) : ℝ := P.P1 * w.wU + P.P0 * w.wE

/-- Table 1, p. 13, with QE(G) = 0 (Lemma 1): cases i (contingent), ii (mixed), iii (diversification),
iv (sole). -/
noncomputable def Params.orderI (P : Params) (w : Prices) : Orders := ⟨(P.m - w.wU) / 2, 0, 0, (P.m - w.wE) / 2⟩
noncomputable def Params.orderII (P : Params) (ρ : ℝ) (w : Prices) : Orders :=
  ⟨(w.wR - P.PG ρ * w.wU - P.PB ρ * w.wE) / (2 * P.PG ρ * P.P0G ρ),
   (P.PG ρ * P.P0G ρ * P.m - w.wR + P.PB ρ * w.wE + P.P1 * w.wU) / (2 * P.PG ρ * P.P0G ρ), 0,
   (w.wR - P.P1 * w.wU - P.P0 * w.wE) / (2 * P.PG ρ * P.P0G ρ)⟩
noncomputable def Params.orderIII (P : Params) (w : Prices) : Orders :=
  ⟨(w.wR - w.wU) / (2 * P.P0), (P.P0 * P.m - w.wR + P.P1 * w.wU) / (2 * P.P0), 0, 0⟩
noncomputable def Params.orderIV (P : Params) (w : Prices) : Orders := ⟨0, (P.m - w.wR) / 2, 0, 0⟩

open Classical in
/-- The buyer's order used in the payoffs (5)–(6): Table 1 by case, with footnote 11's tie-break
(at η1 = wR the buyer sources contingently). -/
noncomputable def Params.order (P : Params) (ρ : ℝ) (w : Prices) : Orders :=
  if w.wR ≤ w.wU then P.orderIV w
  else if P.eta1 ρ w ≤ w.wR then P.orderI w
  else if P.eta2 w < w.wR then P.orderII ρ w
  else P.orderIII w

/-- Supplier R's payoff (5) and supplier U's payoff (6), p. 15. -/
noncomputable def Params.payR (P : Params) (ρ : ℝ) (w : Prices) : ℝ :=
  (w.wR - P.cR) * (P.order ρ w).QR + P.PB ρ * (w.wE - P.cR) * (P.order ρ w).QEB
noncomputable def Params.payU (P : Params) (ρ : ℝ) (w : Prices) : ℝ :=
  (P.P1 * w.wU - P.cU) * (P.order ρ w).QU

/-- Strategy spaces, p. 16: cU/P1 ≤ wU ≤ m and cR ≤ wR ≤ wE ≤ m. -/
def Params.UFeasible (P : Params) (wU : ℝ) : Prop := P.cU / P.P1 ≤ wU ∧ wU ≤ P.m
def Params.RFeasible (P : Params) (wR wE : ℝ) : Prop := P.cR ≤ wR ∧ wR ≤ wE ∧ wE ≤ P.m

/-- Nash equilibrium of the pricing game, p. 16: (wR, wE) maximizes (5) given wU, and wU maximizes (6)
given (wR, wE). -/
def Params.IsNash (P : Params) (ρ : ℝ) (w : Prices) : Prop :=
  P.UFeasible w.wU ∧ P.RFeasible w.wR w.wE ∧
  (∀ wR' wE', P.RFeasible wR' wE' → P.payR ρ ⟨w.wU, wR', wE'⟩ ≤ P.payR ρ w) ∧
  (∀ wU', P.UFeasible wU' → P.payU ρ ⟨wU', w.wR, w.wE⟩ ≤ P.payU ρ w)

/-- "The equilibrium", p. 16: a Pareto-dominant (undominated) Nash equilibrium: no other Nash equilibrium
gives both suppliers at least as much and one of them more. -/
def Params.IsEquilibrium (P : Params) (ρ : ℝ) (w : Prices) : Prop :=
  P.IsNash ρ w ∧ ¬ ∃ w' : Prices, P.IsNash ρ w' ∧ P.payU ρ w ≤ P.payU ρ w' ∧
    P.payR ρ w ≤ P.payR ρ w' ∧ (P.payU ρ w < P.payU ρ w' ∨ P.payR ρ w < P.payR ρ w')

/-- Thresholds ψ1, ψ2, ψ3 (p. 16), ϕ1, ϕ2 (p. 18) and the buyer threshold m − (P1m − cU)/√(4 − P1 + P1²)
of Proposition 4 (p. 22). -/
noncomputable def Params.psi1 (P : Params) : ℝ := (P.P1 * P.m + P.cU) / (2 * P.P1)
noncomputable def Params.psi2 (P : Params) : ℝ := (P.P0 * P.m + 2 * P.cU / P.P1) / (P.P0 + 2)
noncomputable def Params.psi3 (P : Params) : ℝ := (P.P0 + 1) / P.P1 * P.cU - P.P0 * P.m
noncomputable def Params.phi1 (P : Params) : ℝ := ((1 + P.P0) * P.m + P.cU) / 2
noncomputable def Params.phi2 (P : Params) : ℝ := (2 * P.P0 * P.m + P.cU) / (P.P0 + 1)
noncomputable def Params.buyerThreshold (P : Params) : ℝ :=
  P.m - (P.P1 * P.m - P.cU) / Real.sqrt (4 - P.P1 + P.P1 ^ 2)

/-- (wR, wE) is a best response of supplier R to wU under (5), at accuracy ρ. -/
def Params.IsBestResponseR (P : Params) (ρ wU wR wE : ℝ) : Prop :=
  P.RFeasible wR wE ∧ ∀ wR' wE', P.RFeasible wR' wE' → P.payR ρ ⟨wU, wR', wE'⟩ ≤ P.payR ρ ⟨wU, wR, wE⟩

/-- Table 2 (i-a) / (i-b), p. 17 (ρ = 1), with wR at the lower end of the (i-a) interval. -/
noncomputable def Params.priceI (P : Params) : Prices :=
  if P.psi1 < P.cR then
    ⟨P.psi1, P.P1 * P.psi1 + P.P0 * ((P.m + P.cR) / 2), (P.m + P.cR) / 2⟩
  else ⟨P.cR, P.P1 * P.cR + P.P0 * ((P.m + P.cR) / 2), (P.m + P.cR) / 2⟩

/-- The buyer is in case (i) of the order rule: it orders only from U at Time 0 and, after a bad signal,
from R at Time 1. -/
def Params.Contingent (P : Params) (ρ : ℝ) (w : Prices) : Prop :=
  ¬ w.wR ≤ w.wU ∧ P.eta1 ρ w ≤ w.wR

/-- Table 3 (i-a), (i-b), (ii), p. 19 (ρ = 0), with w_R^N = cR in (i) and wE = m (irrelevant at ρ = 0). -/
noncomputable def Params.priceN (P : Params) : Prices :=
  if P.phi1 < P.cR then ⟨P.psi1, P.cR, P.m⟩
  else if P.phi2 < P.cR then ⟨(P.cR - P.P0G 0 * P.m) / P.P1G 0, P.cR, P.m⟩
  else ⟨(P.P0 * P.m + P.cR + 2 * P.cU / P.P1) / (3 + P.P0),
        (2 * P.P0 * P.m + 2 * P.cR + P.cU) / (3 + P.P0), P.m⟩

end ContingentSourcing.Competition


