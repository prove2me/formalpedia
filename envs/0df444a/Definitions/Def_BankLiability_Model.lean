-- Prove2me | Definitions.Def_BankLiability_Model
-- name    : BankLiability_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:14.423998+00:00
-- url     : https://prove2.me/theorems/4f1dd64d-6e1d-44f3-9da1-0bbe1fb871f9
-- title:
--   The static bank model: boundaries $V_b,V_d,V_l$, fair rate $g^\circ$, values $B,E,F$, feasible and strategic structures
-- statement:
--   Fix parameters (Table 1) and an asset value $V>0$. A **liability structure** is a pair $(D,C_B)$ of deposits $D\ge0$ and a nondeposit debt coupon $C_B\ge0$. The model attaches to it the following quantities.
--
--   1. The **regulatory total capital boundary** $V_b=D/(1-\beta)$: the regulator closes the bank when the asset value falls to $V_b$.
--   2. The **state price** of the asset value falling to a boundary $L\le V$: $(L/V)^\lambda$.
--   3. The **fair assessment rate** of deposit insurance, equation (2):
--   $$g^\circ=\frac{r[\alpha-\beta]^+}{1-\beta}\cdot\frac{x^\lambda}{1-x^\lambda},\qquad x=\frac{D/V}{1-\beta}=\frac{V_b}{V};$$
--   the assessment rate $g=(1-\omega)g^\circ$, the premium $I=gD$, and the net deposit cost $C_D=(r-\eta)D$.
--   4. The **value of the insurance contract** to the insurer at rate $g$: $\frac{gD}{r}(1-q)-[D-(1-\alpha)V_b]^+q$ with $q=(V_b/V)^\lambda$ (premiums until closure, minus the loss at closure).
--   5. The **endogenous default boundary**, equation (3): $V_d=(1-\tau)\frac{\lambda}{1+\lambda}\cdot\frac{I+C_D+C_B}{r}$, and the **liquidation boundary** $V_l=\max\{V_b,V_d\}$.
--   6. With $p=(V_l/V)^\lambda$: the **nondeposit debt value** $B=\frac{C_B}{r}(1-p)+[(1-\alpha)V_l-D]^+p$, the **equity value** $E=V-(1-\tau)\frac{I+C_D+C_B}{r}(1-p)-V_lp$ (the equity value for a general boundary $L$ is the same expression with $L$ in place of $V_l$), and the **total bank value of the shareholders** $F=D+B+E$.
--   7. The **credit spread** $s$, defined by $C_B=(r+s)B$.
--   8. The structure is **feasible** when $0\le D<(1-\beta)V$, $C_B\ge0$ and $V_d\le V$ (so $V\ge V_l$), and **strategic** when it is feasible and maximizes $F$ over all feasible structures.
--
--   These are the objects of Propositions 1 and 2: the bank chooses $(D,C_B)$ to maximize the total value of its original shareholders, trading the deposit profit and the tax advantage of debt against the insurance premium and the cost of liquidation.
--
--   **Formalization Note** The paper prices every claim under a geometric Brownian motion and derives the closed forms in an Online Appendix that is not part of the source; the model is stated at the closed-form level, with the state price $(L/V)^\lambda$ as an explicit expression. The paper's closed form of $F$ is also in that appendix; $B$, $E$, $F$ are the displayed pricing equations (15), (16), (17) of §4.1 with no restructuring (hurdle state price $0$, issuance costs $0$), which match the §2 description (dividend $\delta V-(1-\tau)(I+C_D+C_B)$, debt worth $[(1-\alpha)V_l-D]^+$ at liquidation, $F=D+B+E$). As in (2), $g^\circ$ is evaluated at $V_b$ even when $V_d>V_b$. The point $D=(1-\beta)V$ is not feasible because (2) is undefined there. A strategic structure is defined as a maximizer of $F$, never by the closed forms (6). In Lean, $s=C_B/B-r$, which is $-r$ if $B=0$.
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.1–§2.3, pp.4–6 (C_D, C_B=(r+s)B, F=D+B+E p.4; V_b, eq. (2), I=gD p.5; g=(1−ω)g°, eq. (3), V_l, B(V_l) p.6; feasibility and strategic choice §2.3 p.6), and eqs. (15)–(17), pp.14–15, with no restructuring

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam

namespace BankLiability

/-! The static bank model of Sundaresan–Wang, *Strategic Bank Liability Structure Under Capital
Requirements*, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2,
pp.3–7, with the pricing equations (14)–(17) of §4.1 (pp.14–15) in their no-restructuring case.

Throughout, `V > 0` is the asset value, `D` the deposits and `CB` the nondeposit coupon C_B.

**Formalization Note (state-price level).** The paper values every claim under a geometric
Brownian motion (1), p.3; the closed forms it uses are expressions in the state price
`(L/V)^λ` of the asset value reaching a boundary `L ≤ V`, and their derivations are in the Online
Appendix, which is not part of the source artifact. The model is stated at that closed-form level:
the state price is the expression `(L/V)^λ` (`Real.rpow`), not an expectation over a stochastic
process.

**Formalization Note (total bank value).** The paper's closed form of the total bank value is in
the Online Appendix (p.4). It is taken here from the displayed pricing equations (15), (16),
(17) of §4.1 (pp.14–15) with no restructuring: hurdle state price `π_h = 0` (the limit `H → ∞` of
(13)–(14)), issuance costs `θ_D = θ_B = 0`, and liquidation state price `π_l = (V_l/V)^λ`. This
agrees with the §2 description: dividend `δV − (1−τ)(I + C_D + C_B)` (p.4), nondeposit debt worth
`[(1−α)V_l − D]⁺` at liquidation (p.6), and `F = D + B + E` (p.4). -/

/-- **Regulatory total capital boundary** `V_b = D/(1 − β)`, the asset value at which the regulator
closes the bank. Sundaresan–Wang (2023), §2.2, p.5: "V_b − D = βV_b, which implies
V_b = D/(1−β)". -/
noncomputable def regBoundary (P : Params) (D : ℝ) : ℝ := D / (1 - P.beta)

/-- **State price of the asset value reaching the boundary `L`**, `(L/V)^λ`.
Sundaresan–Wang (2023): Proposition 2, p.7 ("π is the state price of regulatory total capital
boundary", with π = (V_b/V)^λ by the proposition's identity V_b/V = π^{1/λ}); (14), p.14, in the
limit of no restructuring hurdle.

**Formalization Note.** For `0 ≤ L ≤ V` this is a number in `[0, 1]`; it is used only for such
`L`. -/
noncomputable def statePriceAt (P : Params) (V L : ℝ) : ℝ := (L / V) ^ lam P

/-- **Fair assessment rate of deposit insurance** g°, equation (2), p.5:
`g° = r[α − β]⁺/(1 − β) · x^λ · (1 − x^λ)⁻¹` with `x = (D/V)/(1 − β)` (so `x = V_b/V`).

**Formalization Note.** `[·]⁺` is `max · 0`. The formula is used for `0 ≤ D < (1 − β)V`, where
`x ∈ [0, 1)`; at `D = (1 − β)V` the paper's formula is undefined, and that point is excluded from
the feasible set `Feasible`. As in (2), g° is evaluated at the regulatory boundary V_b, also when
the endogenous default boundary lies above it (the premium "depends on deposits and the
regulatory total capital boundary", p.14). -/
noncomputable def fairRate (P : Params) (V D : ℝ) : ℝ :=
  P.r * max (P.alpha - P.beta) 0 / (1 - P.beta) * (D / V / (1 - P.beta)) ^ lam P *
    (1 - (D / V / (1 - P.beta)) ^ lam P)⁻¹

/-- **Assessment rate** `g = (1 − ω)g°` (Sundaresan–Wang (2023), §2.2, p.6). -/
noncomputable def assessRate (P : Params) (V D : ℝ) : ℝ := (1 - P.omega) * fairRate P V D

/-- **Deposit insurance premium** `I = gD` (Sundaresan–Wang (2023), §2.2, pp.5–6). -/
noncomputable def premium (P : Params) (V D : ℝ) : ℝ := assessRate P V D * D

/-- **Net cost of serving deposits** `C_D = (r − η)D` (Sundaresan–Wang (2023), §2.1, p.4). -/
def depositCost (P : Params) (D : ℝ) : ℝ := (P.r - P.eta) * D

/-- **Value of the deposit insurance contract to the insurer at assessment rate `g`**: the
present value `gD/r · (1 − q)` of the premiums `gD` received until the regulator closes the bank
at V_b, minus the insurer's loss `[D − (1 − α)V_b]⁺` at closure times its state price
`q = (V_b/V)^λ`. Sundaresan–Wang (2023), §2.2, p.5: the insurer's loss function
`[D − (1−α)V_b]⁺`, the premium `I = gD`, and "The fair insurance premium should make the
insurance contract worth zero to each party of the insurance contract".

**Formalization Note.** The paper derives (2) from this zero-value condition in its Online
Appendix (not held); the expression here is its closed form at the state-price level, with
closure at V_b as in (2). -/
noncomputable def insuranceValue (P : Params) (V D g : ℝ) : ℝ :=
  g * D / P.r * (1 - statePriceAt P V (regBoundary P D)) -
    max (D - (1 - P.alpha) * regBoundary P D) 0 * statePriceAt P V (regBoundary P D)

/-- **Endogenous default boundary as a function of the three liabilities**, equation (3), p.6:
`V_d = (1 − τ) · λ/(1 + λ) · (I + C_D + C_B)/r`. -/
noncomputable def defaultBoundaryOf (P : Params) (I CD CB : ℝ) : ℝ :=
  (1 - P.tau) * (lam P / (1 + lam P)) * ((I + CD + CB) / P.r)

/-- **Endogenous default boundary of the liability structure `(D, C_B)`**: (3) with `I = gD` and
`C_D = (r − η)D` (Sundaresan–Wang (2023), pp.4–6). -/
noncomputable def defaultBoundary (P : Params) (V D CB : ℝ) : ℝ :=
  defaultBoundaryOf P (premium P V D) (depositCost P D) CB

/-- **Liquidation boundary** `V_l = max{V_b, V_d}` (Sundaresan–Wang (2023), §2.2, p.6). -/
noncomputable def liqBoundary (P : Params) (V D CB : ℝ) : ℝ :=
  max (regBoundary P D) (defaultBoundary P V D CB)

/-- **Equity value when the bank is liquidated at the asset value `L`**, for total coupon
`C = I + C_D + C_B`: `V − (1 − τ)C/r · (1 − (L/V)^λ) − L · (L/V)^λ`.
This is (16), p.15, with no restructuring (`π_h = 0`, `π_l = (L/V)^λ`, `L_i V_i = L`).

**Formalization Note.** Used both for the actual liquidation boundary (`equityValue`) and, in the
milestone on (3), for an arbitrary candidate default boundary `L ∈ (0, V]`. -/
noncomputable def equityGivenBoundary (P : Params) (V C L : ℝ) : ℝ :=
  V - (1 - P.tau) * C / P.r * (1 - statePriceAt P V L) - L * statePriceAt P V L

/-- **Value of nondeposit debt** `B = C_B/r · (1 − p) + [(1 − α)V_l − D]⁺ · p`, with
`p = (V_l/V)^λ`: (15), p.14, with no restructuring (`π_h = 0`), and `B(V_l) = [(1−α)V_l − D]⁺`
(p.6). -/
noncomputable def debtValue (P : Params) (V D CB : ℝ) : ℝ :=
  CB / P.r * (1 - statePriceAt P V (liqBoundary P V D CB)) +
    max ((1 - P.alpha) * liqBoundary P V D CB - D) 0 * statePriceAt P V (liqBoundary P V D CB)

/-- **Equity value** `E = V − (1 − τ)(I + C_D + C_B)/r · (1 − p) − V_l · p`, `p = (V_l/V)^λ`:
(16), p.15, with no restructuring. -/
noncomputable def equityValue (P : Params) (V D CB : ℝ) : ℝ :=
  equityGivenBoundary P V (premium P V D + depositCost P D + CB) (liqBoundary P V D CB)

/-- **Total bank value of the shareholders** `F = D + B + E` (Sundaresan–Wang (2023), §2.1, p.4;
(17), p.15, with no restructuring and `θ_D = θ_B = 0`). -/
noncomputable def totalValue (P : Params) (V D CB : ℝ) : ℝ :=
  D + debtValue P V D CB + equityValue P V D CB

/-- **Credit spread of nondeposit debt** `s`, defined by `C_B = (r + s)B` (Sundaresan–Wang (2023),
§2.1, p.4), i.e. `s = C_B/B − r`.

**Formalization Note.** Lean's `x / 0 = 0` gives `s = −r` when `B = 0`; at a strategic structure
`B > 0`, and no hypothesis assumes it. -/
noncomputable def creditSpread (P : Params) (V D CB : ℝ) : ℝ :=
  CB / debtValue P V D CB - P.r

/-- **Feasible liability structures** `(D, C_B)` at asset value `V`: `D ≥ 0`, `C_B ≥ 0`,
`D < (1 − β)V` (the regulatory boundary lies strictly below `V`), and `V_d ≤ V`; together with the
first, these say `V ≥ V_l` (Sundaresan–Wang (2023), §2.3, p.6: "A bank's total capital has to meet
a minimum requirement: V ≥ V_l").

**Formalization Note.** The point `D = (1 − β)V` (where `V = V_b`) is excluded because the fair
rate (2) is undefined there (`x^λ = 1`). -/
def Feasible (P : Params) (V D CB : ℝ) : Prop :=
  0 ≤ D ∧ D < (1 - P.beta) * V ∧ 0 ≤ CB ∧ defaultBoundary P V D CB ≤ V

/-- **Strategic liability structure** (Sundaresan–Wang (2023), §2.3, p.6: "The strategic choice of
liability structure (D*/V, B*/V) maximizes the total value of the original equity holders"):
`(D, C_B)` is feasible and maximizes the total bank value `F` over all feasible structures.

**Formalization Note.** The choice variables are `D` and the coupon `C_B`; the nondeposit debt
value `B` is then determined by `debtValue`. The strategic structure is defined by the
optimization, never by the closed forms (6). -/
def IsStrategic (P : Params) (V D CB : ℝ) : Prop :=
  Feasible P V D CB ∧
    ∀ D' CB' : ℝ, Feasible P V D' CB' → totalValue P V D' CB' ≤ totalValue P V D CB

end BankLiability


