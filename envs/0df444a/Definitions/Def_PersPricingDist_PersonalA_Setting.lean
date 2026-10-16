-- Prove2me | Definitions.Def_PersPricingDist_PersonalA_Setting
-- name    : PersPricingDist_PersonalA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:25.488563+00:00
-- url     : https://prove2.me/theorems/9842d3e5-a4c2-4d1b-93e3-f62e60e737d7
-- title:
--   §2 and §5.2 — valuations, PP and PU continuation outcomes, profits, and channel contributions
-- statement:
--   Consumers have types $x\in[0,X]$. Their values for the manufacturer's direct channel A and retailer B are
--   $$u_A(x)=\max\{1-x,0\},\qquad u_B(x)=\max\{v-sx,0\}. $$
--   The standing regime is $0<s<v<1$ and $X\ge v/s$. The equal-value type is $\hat x=(1-v)/(1-s)$ and its value is $\hat u=(v-s)/(1-s)$. A's monopoly profit with personalized prices is the integral of $u_A$ over consumers. The channels' contributions $\alpha$ and $\beta$ integrate the valuation advantages of A before $\hat x$ and B after it.
--
--   Under PP, both firms set personalized prices. At wholesale price $w$, each consumer's payment follows the selected Bertrand continuation: A charges $u_A(x)$ if $u_B(x)<w$; B charges $u_B(x)$ if $u_A(x)<w\le u_B(x)$; otherwise the higher-valued channel charges $w+|u_A(x)-u_B(x)|$. Industry profit is the integral of those payments. Dual distribution yields a strict gain when some $w\ge0$ produces industry profit above A's monopoly profit.
--
--   Under PU, B announces one retail price $p_B$ and A responds with prices tailored to each consumer. B serves a consumer with positive B valuation if $p_B\le u_B(x)$ and $u_A(x)-u_B(x)+p_B\le w$; otherwise A charges $u_A(x)-u_B(x)+p_B$ when B has an affordable offer, or $u_A(x)$ when it does not. B's profit is $(p_B-w)$ times the Lebesgue measure of its buyers. Dual distribution yields a strict gain if there are $w\ge0$ and a global profit-maximizing $p_B$ at which industry profit exceeds the monopoly profit.
--
--   These outcome and profit definitions are the market objects used throughout the mission. The valuation cutoffs $\tilde v(s)$ and $\check v(s)$ are also defined from displays (4) and (28); their connection to optimal distribution is stated separately.
--
--   **Formalization Note** Indifferent consumers are assigned to B when its offer is feasible, except that consumers with $u_B(x)=0$ are assigned to A. Positive-valuation tie boundaries have measure zero. At $w=0$, types beyond $v/s$ have zero value for both channels over an interval, but their payment is zero under the PP rule; the PU rule assigns them to A. The price maximization ranges over all real numbers; the wholesale price is nonnegative. The fixed fee of the two-part tariff only divides industry profit and is therefore omitted.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84a…c253), pp. 5–9, 12, 16, 18–19; OA pp. 7, 10–11

import Mathlib
noncomputable section

namespace PersPricingDist.PersonalA

/-- The valuation parameters and the largest consumer type in §2. -/
structure Model where
  v : ℝ
  s : ℝ
  X : ℝ

namespace Model

/-- The assumptions maintained in §5 for positively correlated valuations. -/
structure Standing (M : Model) : Prop where
  s_pos : 0 < M.s
  s_lt_v : M.s < M.v
  v_lt_one : M.v < 1
  X_large : M.v / M.s ≤ M.X

/-- A consumer's value for the direct channel. -/
def uA (M : Model) (x : ℝ) : ℝ := max (1 - x) 0

/-- A consumer's value for the retail channel. -/
def uB (M : Model) (x : ℝ) : ℝ := max (M.v - M.s * x) 0

/-- Consumer type at which the two values are equal. -/
def xhat (M : Model) : ℝ := (1 - M.v) / (1 - M.s)

/-- Their common value at `xhat`. -/
def uhat (M : Model) : ℝ := (M.v - M.s) / (1 - M.s)

/-- A's personalized-pricing profit under mono distribution. -/
noncomputable def monoP (M : Model) : ℝ :=
  ∫ x in (0 : ℝ)..M.X, M.uA x

/-- The amount by which A raises the industry's monopoly profit. -/
noncomputable def alpha (M : Model) : ℝ :=
  ∫ x in (0 : ℝ)..M.xhat, (M.uA x - M.uB x)

/-- The amount by which B raises the industry's monopoly profit. -/
noncomputable def beta (M : Model) : ℝ :=
  ∫ x in M.xhat..M.X, (M.uB x - M.uA x)

/-- Consumer expenditure in the PP continuation, with the selected Bertrand equilibrium. -/
def revPP (M : Model) (w x : ℝ) : ℝ :=
  if M.uB x < w then M.uA x
  else if M.uA x < w then M.uB x
  else w + |M.uA x - M.uB x|

/-- Industry profit in PP is total expenditure of consumers. -/
noncomputable def indPP (M : Model) (w : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..M.X, M.revPP w x

/-- Strict gain from dual distribution for some nonnegative wholesale price in PP. -/
def DualPP (M : Model) : Prop :=
  ∃ w : ℝ, 0 ≤ w ∧ M.monoP < M.indPP w

/-- Consumers served by B when B announces its uniform price before A responds. -/
def buysBPU (M : Model) (w pB x : ℝ) : Prop :=
  0 < M.uB x ∧ pB ≤ M.uB x ∧ M.uA x - M.uB x + pB ≤ w

/-- Consumer expenditure in the PU continuation. -/
def revPU (M : Model) (w pB x : ℝ) : ℝ :=
  by
    classical
    exact if M.buysBPU w pB x then pB
      else if 0 < M.uB x ∧ pB ≤ M.uB x then M.uA x - M.uB x + pB
      else M.uA x

/-- The measure of consumers buying from B after A's personalized response. -/
noncomputable def demandBPU (M : Model) (w pB : ℝ) : ℝ :=
  (MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysBPU w pB x}).toReal

/-- B's retail margin times its demand. -/
noncomputable def profBPU (M : Model) (w pB : ℝ) : ℝ :=
  (pB - w) * M.demandBPU w pB

/-- Industry profit in PU is total expenditure of consumers. -/
noncomputable def indPU (M : Model) (w pB : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..M.X, M.revPU w pB x

/-- Strict gain for some wholesale price and a global best response by B. -/
def DualPU (M : Model) : Prop :=
  ∃ w : ℝ, 0 ≤ w ∧ ∃ pB : ℝ,
    IsMaxOn (M.profBPU w) Set.univ pB ∧ M.monoP < M.indPU w pB

/-- The PP cut-off in the valuation parameters, display (4). -/
noncomputable def vTilde (s : ℝ) : ℝ :=
  s * (2 + Real.sqrt (1 - s)) / (1 + s)

/-- The PU cut-off in the valuation parameters, display (28). -/
noncomputable def vCheck (s : ℝ) : ℝ :=
  s * (2 + Real.sqrt ((1 - s) * (2 + 5 * s + s ^ 2) / (1 + 2 * s))) / (1 + s)

end Model

end PersPricingDist.PersonalA


