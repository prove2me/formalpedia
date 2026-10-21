-- Prove2me | Definitions.Def_RefurbCommit_DefectProfit_Model
-- name    : RefurbCommit_DefectProfit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:10.347869+00:00
-- url     : https://prove2.me/theorems/b59973bf-23d0-4f28-ab05-45a4f0f4e3d7
-- title:
--   §3, §4.1, App. B (pp. 5–9, B-1) — two-period durable-goods monopoly with refurbished defective returns: utilities, demands, second-period optimum, subgame-perfect profit Π*, commitment profit Π^C
-- statement:
--   A monopolist sells a durable product over two periods to a continuum of consumers of unit mass whose quality valuations $\theta$ are uniformly distributed on $[0,1]$. A fraction of new units is defective; the **defect rate** $\alpha>0$ is the expected number of extra units needed per unit sold, so a sale of $q$ new units costs $(1+\alpha)c_n q$, and a sale of $q$ refurbished units (defect rate $k_r\alpha$) costs $(1+k_r\alpha)c_r q$. Defective units are exchanged, at a hassle cost $h$ per return.
--
--   **Parameters.** Perceived qualities $v_n$ (new) and $v_r$ (refurbished), marginal costs $c_n$ and $c_r$, the factor $k_r$, the hassle cost $h$ and the common discount factor $\rho$. The standing assumptions are
--   $$0<v_r<v_n,\qquad 0\le c_r<c_n,\qquad 0\le k_r<1,\qquad h\ge 0,\qquad 0<\rho<1 .$$
--   Write $\mu_n=v_n-(1+\alpha)c_n-h\alpha$ and $\mu_r=v_r-(1+k_r\alpha)c_r-hk_r\alpha$.
--
--   **Utilities (3.1).** A consumer of type $\theta$ obtains
--   $$U^\theta_1=v_n\theta-h\alpha-p_1,\quad U^\theta_2=\rho(v_n\theta-h\alpha-p_2),\quad U^\theta_r=\rho(v_r\theta-hk_r\alpha-p_r),\quad U^\theta_0=0$$
--   from buying new in period 1, new in period 2, refurbished in period 2, or nothing.
--
--   **Second period (4.2)–(4.3).** Given first-period sales $q_1$, the remaining types are $[0,1-q_1]$. A remaining type buys new if $U^\theta_2\ge\max\{U^\theta_r,0\}$ and refurbished if $U^\theta_r\ge\max\{U^\theta_2,0\}$; the demands $q_2(q_1,\mathbb P)$, $q_r(q_1,\mathbb P)$ are the Lebesgue measures of these buyer sets. The profit is $\Pi_2=q_2(p_2-(1+\alpha)c_n)+q_r(p_r-(1+k_r\alpha)c_r)$, and the prices $(p_2,p_r)$ are optimal if they satisfy the returns constraint $(1+k_r\alpha)q_r\le\alpha q_1$ and maximize $\Pi_2$ among all prices that satisfy it.
--
--   **First period and $\Pi^*$ (4.4)–(4.5).** A type buys in period 1 if $U^\theta_1\ge\max\{U^\theta_2,U^\theta_r,0\}$ evaluated at the anticipated second-period prices. A subgame-perfect outcome $(p_1,q_1,p_2,p_r)$ is one in which $q_1$ is the measure of first-period buyers at $p_1$ under the anticipation $(p_2,p_r)$, and $(p_2,p_r)$ is optimal in the second period given $q_1$. The firm's profit without commitment is
--   $$\Pi^*(\alpha)=\sup\big\{\,q_1(p_1-(1+\alpha)c_n)+\rho\,\Pi_2(q_1,p_2,p_r)\ :\ (p_1,q_1,p_2,p_r)\ \text{subgame perfect}\,\big\}.$$
--
--   **Commitment (B.19)–(B.20).** If the firm announces $(p_1,p_2,p_r)$ at the start, type $\theta\in[0,1]$ buys the option whose utility is at least the other three; $q^C_1,q^C_2,q^C_r$ are the measures of these buyer sets, and
--   $$\Pi^C(\alpha)=\sup\big\{\,q^C_1(p_1-(1+\alpha)c_n)+\rho q^C_2(p_2-(1+\alpha)c_n)+\rho q^C_r(p_r-(1+k_r\alpha)c_r)\ :\ (1+k_r\alpha)q^C_r\le\alpha q^C_1\,\big\}.$$
--
--   **Thresholds.** $\alpha_c=(v_n-c_n)/(c_n+h)$; $\bar\alpha=(c_rv_n-c_nv_r)/(v_r(c_n+h)-v_n(c_r+h)k_r)$; $\underline q_1=\max\{(\mu_n-\mu_r)/(v_n-v_r),\ \mu_n(1+k_r\alpha)/(v_n(1+k_r\alpha)+2\alpha v_r)\}$; $\bar q_1=\max\{\mu_n/v_n,\mu_r/v_r\}$; $\bar v_r=(A+\sqrt{A^2+4\rho\alpha v_n(1+k_r\alpha)(v_r-\mu_r)})/(2\rho\alpha)$ with $A=\alpha(\mu_n+\rho(v_r-\mu_r))-(1+k_r\alpha)(v_n-\mu_n)$. The **Figure 3 parameters** are $c_n=0.7$, $c_r=0.1$, $v_n=1$, $\rho=0.9$, $k_r=0.25$, $h=0.05$ with $v_r$ free.
--
--   These objects are shared by every statement of the mission: Proposition 3 compares $\Pi^*$ and $\Pi^C$ as functions of the defect rate.
--
--   **Formalization Note** Demands are measures of buyer sets built from the purchase rules, not the closed forms (4.2), (4.4), (B.19), which omit the clipping of $\theta$ to $[0,1]$. A consumer indifferent between two options counts in both buyer sets (the overlaps have measure zero). $\Pi^*$ and $\Pi^C$ are real suprema (`sSup`); the commitment set always contains $0$ and both are bounded above in truth. The added assumption $v_r>0$ is used by (4.2), which divides by $v_r$. The paper's bound $h<\bar h=(v_n-v_r)c_n(1+\alpha)/(\alpha(v_r-v_nk_r))$ (for $k_r<v_r/v_n$, p. 8) is not imposed; the paper's restriction to positive two-period profit appears in the individual theorems where it is used.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), pp. 5–9 (PDF 6–10), §3, §4.1, eqs. (3.1), (4.2)–(4.5); p. A-1 (PDF 34), thresholds ᾱ, q̲1, q̄1; p. A-5 (PDF 38), αc; p. B-1 (PDF 42), eqs. (B.19)–(B.20); p. B-2 (PDF 43), v̄r; p. 15 (PDF 16), Figure 3 parameters (vr free, as in Figure 4(a), p. 16 (PDF 17))

import Mathlib

open MeasureTheory

noncomputable section

namespace RefurbCommit.DefectProfit

/-- Parameters of the two-period model (§3): perceived qualities `vn` (new) and `vr`
(refurbished), marginal costs `cn` (producing a new unit) and `cr` (refurbishing a
defective return), the relative defect factor `kr` of a refurbished unit, the hassle
cost `h` of returning a defective unit, and the common discount factor `rho` (ρ). The
defect rate `α` is not a field: it is an argument of every function below. -/
structure Params where
  vn : ℝ
  vr : ℝ
  cn : ℝ
  cr : ℝ
  kr : ℝ
  h : ℝ
  rho : ℝ

/-- Standing assumptions of §3: `vn > vr` (p. 6), `0 ≤ cr < cn` (p. 6), `kr ∈ [0, 1)`
(p. 7), `h ≥ 0`, `ρ ∈ (0, 1)` (p. 7), and the added `vr > 0` ((4.2) divides by `vr`). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.vr ∧ P.vr < P.vn ∧ 0 ≤ P.cr ∧ P.cr < P.cn ∧ 0 ≤ P.kr ∧ P.kr < 1 ∧
    0 ≤ P.h ∧ 0 < P.rho ∧ P.rho < 1

/-- `µn = vn − (1 + α) cn − h α` (p. 9). -/
def mun (P : Params) (α : ℝ) : ℝ := P.vn - (1 + α) * P.cn - P.h * α

/-- `µr = vr − (1 + kr α) cr − h kr α` (p. 9). -/
def mur (P : Params) (α : ℝ) : ℝ := P.vr - (1 + P.kr * α) * P.cr - P.h * P.kr * α

/-- (3.1): discounted net utility of type `θ` from the new product in period 1 at price `p1`. -/
def U1 (P : Params) (α p1 θ : ℝ) : ℝ := P.vn * θ - P.h * α - p1

/-- (3.1): discounted net utility of type `θ` from the new product in period 2 at price `p2`. -/
def U2 (P : Params) (α p2 θ : ℝ) : ℝ := P.rho * (P.vn * θ - P.h * α - p2)

/-- (3.1): discounted net utility of type `θ` from the refurbished product (period 2, price `pr`). -/
def Ur (P : Params) (α pr θ : ℝ) : ℝ := P.rho * (P.vr * θ - P.h * P.kr * α - pr)

/-! ### Second period (§4.1, (4.2)–(4.3)) -/

/-- Second-period buyers of the new product: remaining types `θ ∈ [0, 1 − q1]` with
`U2 ≥ max {Ur, 0}`. -/
def newBuyers2 (P : Params) (α q1 p2 pr : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Icc 0 (1 - q1) ∧ max (Ur P α pr θ) 0 ≤ U2 P α p2 θ}

/-- Second-period buyers of the refurbished product: remaining types with `Ur ≥ max {U2, 0}`. -/
def refBuyers2 (P : Params) (α q1 p2 pr : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Icc 0 (1 - q1) ∧ max (U2 P α p2 θ) 0 ≤ Ur P α pr θ}

/-- Second-period sales of the new product: the Lebesgue measure of its buyer set
(types are uniform on `[0, 1]`, market size one). -/
def q2 (P : Params) (α q1 p2 pr : ℝ) : ℝ := (volume (newBuyers2 P α q1 p2 pr)).toReal

/-- Second-period sales of the refurbished product. -/
def qr (P : Params) (α q1 p2 pr : ℝ) : ℝ := (volume (refBuyers2 P α q1 p2 pr)).toReal

/-- (4.3): second-period profit `Π2(q1, P)`. -/
def profit2 (P : Params) (α q1 p2 pr : ℝ) : ℝ :=
  q2 P α q1 p2 pr * (p2 - (1 + α) * P.cn) + qr P α q1 p2 pr * (pr - (1 + P.kr * α) * P.cr)

/-- (4.3): the DPR constraint `α q1 ≥ (1 + kr α) qr` (`q2, qr ≥ 0` hold automatically). -/
def Feasible2 (P : Params) (α q1 p2 pr : ℝ) : Prop :=
  (1 + P.kr * α) * qr P α q1 p2 pr ≤ α * q1

/-- `(p2, pr)` solves the second-period problem (4.3) given first-period sales `q1`. -/
def IsOpt2 (P : Params) (α q1 p2 pr : ℝ) : Prop :=
  Feasible2 P α q1 p2 pr ∧
    ∀ p2' pr', Feasible2 P α q1 p2' pr' → profit2 P α q1 p2' pr' ≤ profit2 P α q1 p2 pr

/-! ### First period and the subgame-perfect profit `Π*` (§4.1, (4.4)–(4.5)) -/

/-- Types `θ ∈ [0, 1]` that buy the new product in period 1 at price `p1` when they
anticipate second-period prices `(p2, pr)`: `U1 ≥ max {U2, Ur, 0}`. -/
def buyers1 (P : Params) (α p1 p2 pr : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Icc 0 1 ∧ max (U2 P α p2 θ) (max (Ur P α pr θ) 0) ≤ U1 P α p1 θ}

/-- A subgame-perfect outcome `(p1, q1, p2, pr)`: `q1` is the first-period demand at `p1`
when consumers anticipate `(p2, pr)`, and `(p2, pr)` is the firm's optimal second-period
response to `q1` (consumers' anticipated prices equal `p2*(q1)`, `pr*(q1)`, p. 9). -/
def IsSPOutcome (P : Params) (α p1 q1 p2 pr : ℝ) : Prop :=
  q1 = (volume (buyers1 P α p1 p2 pr)).toReal ∧ IsOpt2 P α q1 p2 pr

/-- (4.5): total discounted profit of an outcome. -/
def totalProfit (P : Params) (α p1 q1 p2 pr : ℝ) : ℝ :=
  q1 * (p1 - (1 + α) * P.cn) + P.rho * profit2 P α q1 p2 pr

/-- `Π*(α)`: the firm's optimal two-period profit without commitment, the supremum of
(4.5) over subgame-perfect outcomes. -/
def PiStar (P : Params) (α : ℝ) : ℝ :=
  sSup {v | ∃ p1 q1 p2 pr, IsSPOutcome P α p1 q1 p2 pr ∧ v = totalProfit P α p1 q1 p2 pr}

/-! ### Commitment scenario (Appendix B, (B.19)–(B.20)) -/

/-- Commitment: types buying the new product in period 2, `U2 ≥ max {U1, Ur, 0}`. -/
def buyersC2 (P : Params) (α p1 p2 pr : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Icc 0 1 ∧ max (U1 P α p1 θ) (max (Ur P α pr θ) 0) ≤ U2 P α p2 θ}

/-- Commitment: types buying the refurbished product, `Ur ≥ max {U1, U2, 0}`. -/
def buyersCr (P : Params) (α p1 p2 pr : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Icc 0 1 ∧ max (U1 P α p1 θ) (max (U2 P α p2 θ) 0) ≤ Ur P α pr θ}

/-- Commitment demand for the new product in period 1 (`U1 ≥ max {U2, Ur, 0}`). -/
def q1C (P : Params) (α p1 p2 pr : ℝ) : ℝ := (volume (buyers1 P α p1 p2 pr)).toReal

/-- Commitment demand for the new product in period 2. -/
def q2C (P : Params) (α p1 p2 pr : ℝ) : ℝ := (volume (buyersC2 P α p1 p2 pr)).toReal

/-- Commitment demand for the refurbished product. -/
def qrC (P : Params) (α p1 p2 pr : ℝ) : ℝ := (volume (buyersCr P α p1 p2 pr)).toReal

/-- (B.20): the commitment objective. -/
def objC (P : Params) (α p1 p2 pr : ℝ) : ℝ :=
  q1C P α p1 p2 pr * (p1 - (1 + α) * P.cn) + P.rho * q2C P α p1 p2 pr * (p2 - (1 + α) * P.cn)
    + P.rho * qrC P α p1 p2 pr * (pr - (1 + P.kr * α) * P.cr)

/-- (B.20): the DPR constraint `α q1 ≥ (1 + kr α) qr`. -/
def FeasibleC (P : Params) (α p1 p2 pr : ℝ) : Prop :=
  (1 + P.kr * α) * qrC P α p1 p2 pr ≤ α * q1C P α p1 p2 pr

/-- `Π^C(α)`: the optimal commitment profit, the supremum of (B.20) over feasible prices. -/
def PiC (P : Params) (α : ℝ) : ℝ :=
  sSup {v | ∃ p1 p2 pr, FeasibleC P α p1 p2 pr ∧ v = objC P α p1 p2 pr}

/-! ### Thresholds named in the proofs -/

/-- `αc = (vn − cn)/(cn + h)` (proof of Proposition 3(ii)(a), p. A-5). -/
def alphaC (P : Params) : ℝ := (P.vn - P.cn) / (P.cn + P.h)

/-- `ᾱ = (cr vn − cn vr)/(vr (cn + h) − vn (cr + h) kr)` (proof of Proposition 1, p. A-1). -/
def alphaBar (P : Params) : ℝ :=
  (P.cr * P.vn - P.cn * P.vr) / (P.vr * (P.cn + P.h) - P.vn * (P.cr + P.h) * P.kr)

/-- `q̲1 = max {(µn − µr)/(vn − vr), µn (1 + kr α)/(vn (1 + kr α) + 2 α vr)}` (p. A-1). -/
def qLow (P : Params) (α : ℝ) : ℝ :=
  max ((mun P α - mur P α) / (P.vn - P.vr))
    (mun P α * (1 + P.kr * α) / (P.vn * (1 + P.kr * α) + 2 * α * P.vr))

/-- `q̄1 = max {µn/vn, µr/vr}` (p. A-1). -/
def qBar (P : Params) (α : ℝ) : ℝ := max (mun P α / P.vn) (mur P α / P.vr)

/-- `A = α (µn + ρ (vr − µr)) − (1 + kr α)(vn − µn)` (proof of Proposition 7, p. B-2). -/
def bigA (P : Params) (α : ℝ) : ℝ :=
  α * (mun P α + P.rho * (P.vr - mur P α)) - (1 + P.kr * α) * (P.vn - mun P α)

/-- `v̄r = (A + √(A² + 4 ρ α vn (1 + kr α)(vr − µr)))/(2 ρ α)` (p. B-2). Note that
`vr − µr = (1 + kr α) cr + h kr α` does not involve `vr`. -/
def vrBar (P : Params) (α : ℝ) : ℝ :=
  (bigA P α + Real.sqrt (bigA P α ^ 2 + 4 * P.rho * α * P.vn * (1 + P.kr * α) * (P.vr - mur P α)))
    / (2 * P.rho * α)

/-- The parameters of Figure 3 (p. 15): `cn = 0.7`, `cr = 0.1`, `vn = 1`, `ρ = 0.9`,
`kr = 0.25`, `h = 0.05`, with `vr` free. -/
def fig3 (vr : ℝ) : Params where
  vn := 1
  vr := vr
  cn := 7 / 10
  cr := 1 / 10
  kr := 1 / 4
  h := 1 / 20
  rho := 9 / 10

end RefurbCommit.DefectProfit


