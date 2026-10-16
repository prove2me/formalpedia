-- Prove2me | Definitions.Def_PersPricingDist_UniformA_Setting
-- name    : PersPricingDist_UniformA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:25.724757+00:00
-- url     : https://prove2.me/theorems/08902cd8-f0ee-4fd7-9ead-05f74b0193db
-- title:
--   §2 and §5.1 — the market, consumer choices, retail profits, and equilibrium conditions
-- statement:
--   Consumers are indexed by $x\in[0,X]$ and have values $u_A(x)=\max\{1-x,0\}$ and $u_B(x)=\max\{v-sx,0\}$. The standing case is $0<s<v<1$ and $X\ge v/s$. The equal-valuation type and value are $\hat x=(1-v)/(1-s)$ and $\hat u=(v-s)/(1-s)$.
--
--   With A alone at uniform price $p$, its profit is $p$ times the mass of consumers who buy. Under uniform prices $(p_A,p_B)$, consumers choose the option with highest nonnegative net utility. A receives $p_A D_A+wD_B$, B receives $(p_B-w)D_B$, and total industry profit is $p_A D_A+p_B D_B$. A downstream Nash equilibrium is a pair of global best responses over real prices.
--
--   When A sets a uniform price before B personalizes, B serves a consumer exactly when $u_B(x)-w>\max\{u_A(x)-p_A,0\}$, charging $u_B(x)-\max\{u_A(x)-p_A,0\}$. Otherwise A sells when its net utility is nonnegative. A receives its retail revenue plus $w$ per B sale. Industry profit is the integral of actual consumer payments. The candidate wholesale and retail prices are the printed formulas of Online Appendix A.
--
--   These definitions are the market model against which Proposition 3 and its supporting price and profit calculations are stated. **Formalization Note** Lebesgue mass represents the unit density of consumers on $[0,X]$. Indifference goes to A in UU; in UP, B serves only with a strictly positive margin. The fixed fee only divides surplus and does not enter industry profit. The wholesale price is constrained to be nonnegative in the goal.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), pp. 5–9, 12; OA pp. 1–3 (PDF 7–11, 14, 34–36)

import Mathlib

namespace PersPricingDist.UniformA

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The market primitives in §2: the retailer's intercept and slope, and the upper
end of the interval of consumer types. -/
structure Model where
  v : ℝ
  s : ℝ
  X : ℝ

namespace Model

/-- The standing assumptions in §2 and §5.1, including the restriction `X ≥ v/s`
of p. 12. -/
structure Standing (M : Model) : Prop where
  s_pos : 0 < M.s
  s_lt_v : M.s < M.v
  v_lt_one : M.v < 1
  market_large : M.v / M.s ≤ M.X

/-- Valuation for A's direct channel (p. 6). -/
def uA (_M : Model) (x : ℝ) : ℝ := max (1 - x) 0
/-- Valuation for B's retail channel (p. 6). -/
def uB (M : Model) (x : ℝ) : ℝ := max (M.v - M.s * x) 0
/-- The equal-valuation consumer type of p. 6. -/
def xhat (M : Model) : ℝ := (1 - M.v) / (1 - M.s)
/-- The common valuation at `xhat`, p. 6. -/
def uhat (M : Model) : ℝ := (M.v - M.s) / (1 - M.s)

/-- Demand is the Lebesgue mass of a set of consumers inside `[0,X]`. -/
noncomputable def demand (M : Model) (P : ℝ → Prop) : ℝ :=
  (MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x}).toReal

/-- In mono distribution, a consumer buys from A at or above zero net utility. -/
def buysMono (M : Model) (p x : ℝ) : Prop := M.uA x ≥ p
/-- A's mono-distribution profit at a uniform price, p. 13. -/
noncomputable def monoProfitU (M : Model) (p : ℝ) : ℝ :=
  p * M.demand (M.buysMono p)

/-- With both prices uniform, ties between A and B go to A; ties with nonpurchase
also go to A. -/
def buysA_UU (M : Model) (pA pB x : ℝ) : Prop :=
  0 ≤ M.uA x - pA ∧ M.uB x - pB ≤ M.uA x - pA
/-- B receives a consumer when it strictly beats A and weakly beats nonpurchase. -/
def buysB_UU (M : Model) (pA pB x : ℝ) : Prop :=
  0 ≤ M.uB x - pB ∧ M.uA x - pA < M.uB x - pB
noncomputable def DA_UU (M : Model) (pA pB : ℝ) : ℝ :=
  M.demand (M.buysA_UU pA pB)
noncomputable def DB_UU (M : Model) (pA pB : ℝ) : ℝ :=
  M.demand (M.buysB_UU pA pB)
/-- A's retail receipts plus wholesale receipts, gross of fixed fee, OA p. 1. -/
noncomputable def profA_UU (M : Model) (w pA pB : ℝ) : ℝ :=
  pA * M.DA_UU pA pB + w * M.DB_UU pA pB
/-- B's retail margin, gross of fixed fee, OA p. 1. -/
noncomputable def profB_UU (M : Model) (w pA pB : ℝ) : ℝ :=
  (pB - w) * M.DB_UU pA pB
/-- Industry profit is the retail payments received from consumers. -/
noncomputable def indUU (M : Model) (pA pB : ℝ) : ℝ :=
  pA * M.DA_UU pA pB + pB * M.DB_UU pA pB
/-- Global downstream Nash equilibrium, with deviations over all real prices. -/
def IsNashUU (M : Model) (w pA pB : ℝ) : Prop :=
  (∀ p : ℝ, M.profA_UU w p pB ≤ M.profA_UU w pA pB) ∧
  (∀ p : ℝ, M.profB_UU w pA p ≤ M.profB_UU w pA pB)

/-- In UP, B serves a consumer precisely where it can earn a positive margin
while beating A's positive surplus and the outside option, OA p. 3. -/
def buysB_UP (M : Model) (w pA x : ℝ) : Prop :=
  max (M.uA x - pA) 0 < M.uB x - w
/-- When B does not serve, A sells to consumers with nonnegative surplus. -/
def buysA_UP (M : Model) (w pA x : ℝ) : Prop :=
  ¬ M.buysB_UP w pA x ∧ pA ≤ M.uA x
noncomputable def DA_UP (M : Model) (w pA : ℝ) : ℝ :=
  M.demand (M.buysA_UP w pA)
noncomputable def DB_UP (M : Model) (w pA : ℝ) : ℝ :=
  M.demand (M.buysB_UP w pA)
/-- The personalized price paid to B by a consumer whom B serves, OA p. 3. -/
def pB_UP (M : Model) (pA x : ℝ) : ℝ :=
  M.uB x - max (M.uA x - pA) 0
/-- The actual consumer payment in the selected UP continuation outcome. -/
noncomputable def paidUP (M : Model) (w pA x : ℝ) : ℝ :=
  if M.buysB_UP w pA x then M.pB_UP pA x
  else if pA ≤ M.uA x then pA else 0
/-- Manufacturer A's receipts, including wholesale revenue, gross of F. -/
noncomputable def profA_UP (M : Model) (w pA : ℝ) : ℝ :=
  pA * M.DA_UP w pA + w * M.DB_UP w pA
/-- Industry profit is the integral of actual consumer payments. -/
noncomputable def indUP (M : Model) (w pA : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..M.X, M.paidUP w pA x
/-- Global optimum for the uniform-price leader A at a given wholesale price. -/
def IsLeaderOptUP (M : Model) (w pA : ℝ) : Prop :=
  ∀ p : ℝ, M.profA_UP w p ≤ M.profA_UP w pA

/-- The candidate wholesale price in regime UU, OA p. 2. -/
def wUU (M : Model) : ℝ :=
  M.s * (4 * (1 + M.v) + M.s) / (2 * (4 + 5 * M.s))
/-- The candidate UU retail price of A, OA p. 2. -/
def pA_UU (M : Model) (w : ℝ) : ℝ :=
  (2 - M.s + 3 * w - M.v) / (4 - M.s)
/-- The candidate UU retail price of B, OA p. 2. -/
def pB_UU (M : Model) (w : ℝ) : ℝ :=
  (M.v * (2 - M.s) + w * (2 + M.s) - M.s) / (4 - M.s)
/-- The candidate wholesale price in regime UP, OA p. 3. -/
def wUP (M : Model) : ℝ := M.s * (1 + M.v) / (2 * (1 + M.s))
/-- The candidate UP leader price, OA p. 3. -/
def pA_UP (M : Model) (w : ℝ) : ℝ := w + (1 - M.v) / 2

end Model
end
end PersPricingDist.UniformA


