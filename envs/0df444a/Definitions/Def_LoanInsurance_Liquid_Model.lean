-- Prove2me | Definitions.Def_LoanInsurance_Liquid_Model
-- name    : LoanInsurance_Liquid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:32:42.921483+00:00
-- url     : https://prove2.me/theorems/48cbff00-f095-4c3f-aac4-39d83f1fddde
-- title:
--   §2, §2.1, §3, Definitions 1 and 3, (2)–(5), (33), (35), pp. 7–16, 39–42 — lending with screening, loan insurance and segmented loan markets; liquid equilibrium
-- statement:
--   This file sets up the model of Ahnert and Kuncl: lending with costly screening, optional loan insurance at origination, and secondary markets for insured and uninsured loans at an interim date.
--
--   **Primitives (§2).** There are dates $t=0,1,2$ and a continuum of lenders $i\in[0,1]$. A loan pays $A>0$ at $t=2$ with probability $\mu\in(0,1)$ without screening and $\psi\in(\mu,1)$ with screening, and $0$ otherwise. Lender $i$'s screening cost $\eta_i$ is private and distributed with distribution function $F$ supported on $[0,\bar\eta]$. At $t=1$ each lender privately learns its loan's payoff $A_i\in\{0,A\}$ and a liquidity shock $\lambda_i\in\{1,\lambda\}$ with $\lambda>1$ and $\Pr\{\lambda_i=\lambda\}=\nu\in(0,1)$; utility is $\lambda_i c_{i1}+c_{i2}-\eta_i s_i$. At $t=0$ a lender may insure the loan for a fee $k$ paid at $t=2$, turning its payoff into the safe payoff $\pi=A-k$. At $t=1$ loans can be sold to competitive outside financiers in two segmented markets, for insured loans at price $p_I$ and for uninsured loans at price $p_U$.
--
--   **Derived quantities.** With $\kappa\equiv\nu\lambda+1-\nu$ and $D'\equiv\nu\lambda+(1-\nu)(1-\mu)$,
--   $$\underline\psi=\frac{\lambda\mu}{\lambda\mu+\kappa(1-\mu)},\qquad \tilde\lambda_L=\frac1{2\mu}+\sqrt{\frac1{4\mu^2}+\frac{(1-\mu)(1-\nu)}{\mu\nu}},$$
--   $$\eta^*=\frac{(1-\nu)(1-\mu)(\psi-\mu)\kappa A}{D'},\qquad p^*_U=\frac{\nu\lambda\mu A}{D'},\qquad m^*=1-\frac{(\kappa(1-\mu)\psi-(1-\psi)\lambda\mu)F(\eta^*)}{\mu(\lambda-1)(1-\nu)(1-\mu)(1-F(\eta^*))}.$$
--   The break-even prices of uninsured loans are (4) without insurance and (33) when a share $m$ of high-cost lenders insures, both at screening threshold $\eta$:
--   $$p^{(4)}(\eta)=\nu A\frac{\psi F(\eta)+\mu(1-F(\eta))}{\nu+(1-\nu)[(1-\psi)F(\eta)+(1-\mu)(1-F(\eta))]},$$
--   $$p^{(33)}(\eta,m)=\nu A\frac{\psi F(\eta)+\mu(1-F(\eta))(1-m)}{\nu[F+(1-F)(1-m)]+(1-\nu)[(1-\psi)F+(1-\mu)(1-F)(1-m)]}.$$
--   Condition (35) is $p^{(4)}(\eta^*)/A<\nu\lambda\mu/D'$.
--
--   **Payoffs.** The value of an uninsured loan repaid with probability $q$ is
--   $$\nu\big(q\max(\lambda p_U,A)+(1-q)\max(\lambda p_U,0)\big)+(1-\nu)\big(q\max(p_U,A)+(1-q)\max(p_U,0)\big),$$
--   i.e. each lender sells at $t=1$ exactly when selling is optimal; an insured loan is worth $\nu\max(\lambda p_I,\pi)+(1-\nu)\max(p_I,\pi)$. A lender with cost $\eta$ choosing screening $s$ and insurance $\ell$ gets the corresponding value minus $\eta s$.
--
--   **Liquid equilibrium with insurance (Definition 1).** A profile consists of a screening threshold $\eta$ (lenders with cost at most $\eta$ screen), the share $m_L$ of screeners and the share $m$ of high-cost lenders who insure, prices $p_I,p_U$ and a fee $k$. It is a liquid equilibrium when: $0\le\eta\le\bar\eta$ and $m_L,m\in[0,1]$; every action used by a positive share of some cost type is optimal among all four choices $(s,\ell)$; the insurer breaks even, $k\,(m_LF(\eta)+m(1-F(\eta)))=A\,(m_LF(\eta)(1-\psi)+m(1-F(\eta))(1-\mu))$; buyers of insured loans break even, $p_I=A-k$; buyers of uninsured loans break even given the sales (3) (all shocked owners sell, unshocked owners sell lemons); and the liquidity condition (2), $\lambda p_U\ge A$, holds. **Definition 3** (no insurance) is the analogue with $\ell\equiv0$, price (4), and (2). The no-insurance system (4)–(5) collects the pairs $(\eta_0,p_0)$ with $\eta_0\in[0,\bar\eta]$, $p_0=p^{(4)}(\eta_0)$ and $\eta_0=(1-\nu)(\psi-\mu)(A-p_0)$.
--
--   These objects are shared by every statement of the mission: Lemma 1, Proposition 1 and Proposition 2 are all statements about them.
--
--   **Formalization Note** The liquidity-shock size $\lambda$ is called `lam`, $\bar\eta$ is `etaBar`. The paper's density $f>0$ on $[0,\bar\eta]$ is replaced by its consequences used in the paper: $F$ continuous and strictly increasing on $[0,\bar\eta]$, $F=0$ on $(-\infty,0]$ and $F=1$ on $[\bar\eta,\infty)$. Strategy profiles are threshold–share profiles, the paper's own reduction (p. 10, "Without loss of generality, lenders use a threshold strategy"). The break-even line for uninsured loans uses the sales (3), which are optimal exactly when (2) holds and $p_U\le A$; at $\lambda p_U=A$ shocked owners of good loans are indifferent and (3) has them sell. The insurer is default-free (p. 2). Neither $k=(1-\mu)A$ nor $p_I=\mu A$ is built in: both come from break-even (Proposition 1).
-- source:
--   Ahnert & Kuncl, Loan Insurance, Market Liquidity, and Lending Standards, Bank of Canada Staff Working Paper 2019-47 (last updated August 2020), pp. 7–16 (PDF 11–20), 39 (PDF 43), 41–42 (PDF 45–46): §2, §2.1, §3, Definition 1, Definition 3, (1)–(5), (33), (35); bounds ψ̲ (B.2, p. 41), λ̃_L, η*, p*_U, m* (Proposition 2, p. 15)

import Mathlib

namespace LoanInsurance.Liquid

/-- Primitives of the model of §2 (pp. 7–9). `lam` is the paper's liquidity-shock size `λ > 1`
(p. 8), `etaBar` the upper end `η̄` of the support of screening costs, and `F` their
cumulative distribution function (p. 8). -/
structure Params where
  /-- loan repayment `A` (p. 8) -/
  A : ℝ
  /-- repayment probability without screening (p. 8) -/
  μ : ℝ
  /-- repayment probability with screening (p. 8) -/
  ψ : ℝ
  /-- probability of the liquidity shock, `Pr{λ_i = λ} = ν` (p. 8) -/
  ν : ℝ
  /-- size `λ` of the liquidity shock (p. 8) -/
  lam : ℝ
  /-- upper end `η̄` of the support of screening costs (p. 8) -/
  etaBar : ℝ
  /-- cumulative distribution function of screening costs (p. 8) -/
  F : ℝ → ℝ

namespace Params

variable (P : Params)

/-- Standing assumptions of §2 (pp. 7–8): `A > 0`, `0 < μ < ψ < 1`, `0 < ν < 1`, `λ > 1`, and
`F` a continuous distribution function supported on `[0, η̄]`, strictly increasing there. -/
def Standing : Prop :=
  0 < P.A ∧ 0 < P.μ ∧ P.μ < P.ψ ∧ P.ψ < 1 ∧ 0 < P.ν ∧ P.ν < 1 ∧ 1 < P.lam ∧ 0 < P.etaBar ∧
    P.F 0 = 0 ∧ P.F P.etaBar = 1 ∧ StrictMonoOn P.F (Set.Icc 0 P.etaBar) ∧
    ContinuousOn P.F (Set.Icc 0 P.etaBar) ∧ (∀ x ≤ 0, P.F x = 0) ∧
    (∀ x, P.etaBar ≤ x → P.F x = 1)

/-- `κ ≡ νλ + 1 − ν` (p. 10). -/
noncomputable def kappa : ℝ := P.ν * P.lam + 1 - P.ν

/-- The bound `ψ̲ ≡ λμ / (λμ + κ(1 − μ))` (Appendix B.2, p. 41). -/
noncomputable def psiUnder : ℝ := P.lam * P.μ / (P.lam * P.μ + P.kappa * (1 - P.μ))

/-- The bound `λ̃_L ≡ 1/(2μ) + √(1/(4μ²) + (1 − μ)(1 − ν)/(μν))` (Proposition 2, p. 15). -/
noncomputable def lamTildeL : ℝ :=
  1 / (2 * P.μ) + Real.sqrt (1 / (4 * P.μ ^ 2) + (1 - P.μ) * (1 - P.ν) / (P.μ * P.ν))

/-- `D′ ≡ νλ + (1 − ν)(1 − μ)` (Appendix B.3, p. 43). -/
noncomputable def Dp : ℝ := P.ν * P.lam + (1 - P.ν) * (1 - P.μ)

/-- `η* = (1 − ν)(1 − μ)(ψ − μ)κA / (νλ + (1 − ν)(1 − μ))` (Proposition 2, part 2). -/
noncomputable def etaStar : ℝ :=
  (1 - P.ν) * (1 - P.μ) * (P.ψ - P.μ) * P.kappa * P.A / P.Dp

/-- `p*_U = νλμA / (νλ + (1 − ν)(1 − μ))` (Proposition 2, part 2). -/
noncomputable def pUStar : ℝ := P.ν * P.lam * P.μ * P.A / P.Dp

/-- `m* = 1 − (κ(1 − μ)ψ − (1 − ψ)λμ) F(η*) / (μ(λ − 1)(1 − ν)(1 − μ)(1 − F(η*)))`
(Proposition 2, part 2). -/
noncomputable def mStar : ℝ :=
  1 - (P.kappa * (1 - P.μ) * P.ψ - (1 - P.ψ) * P.lam * P.μ) * P.F P.etaStar /
    (P.μ * (P.lam - 1) * (1 - P.ν) * (1 - P.μ) * (1 - P.F P.etaStar))

/-- The price of uninsured loans without insurance, (4) (p. 11), at screening threshold `η`. -/
noncomputable def price4 (η : ℝ) : ℝ :=
  P.ν * P.A * (P.ψ * P.F η + P.μ * (1 - P.F η)) /
    (P.ν + (1 - P.ν) * ((1 - P.ψ) * P.F η + (1 - P.μ) * (1 - P.F η)))

/-- The price of uninsured loans with insurance, (33) (p. 41), at screening threshold `η` when a
share `m` of high-cost lenders insures. -/
noncomputable def price33 (η m : ℝ) : ℝ :=
  P.ν * P.A * (P.ψ * P.F η + P.μ * (1 - P.F η) * (1 - m)) /
    (P.ν * (P.F η + (1 - P.F η) * (1 - m)) +
      (1 - P.ν) * ((1 - P.ψ) * P.F η + (1 - P.μ) * (1 - P.F η) * (1 - m)))

/-- Condition (35) (p. 42), evaluated at the screening threshold `η* = η(μ, λ)` of
Proposition 2: insurance is used. -/
def Cond35 : Prop :=
  P.ν * (P.ψ * P.F P.etaStar + P.μ * (1 - P.F P.etaStar)) /
      (P.ν + (1 - P.ν) * ((1 - P.ψ) * P.F P.etaStar + (1 - P.μ) * (1 - P.F P.etaStar))) <
    P.ν * P.lam * P.μ / (P.ν * P.lam + (1 - P.ν) * (1 - P.μ))

/-- Value at `t = 0` of an uninsured loan repaid (`A_i = A`) with probability `q`, when the lender
sells it at `t = 1` at price `pU` exactly when that is optimal (Definition 1.1): with probability
`ν` the lender has the shock and values interim consumption at `λ`, otherwise at `1`. -/
noncomputable def valUninsured (pU q : ℝ) : ℝ :=
  P.ν * (q * max (P.lam * pU) P.A + (1 - q) * max (P.lam * pU) 0) +
    (1 - P.ν) * (q * max pU P.A + (1 - q) * max pU 0)

/-- Value at `t = 0` of an insured loan with safe payoff `piSafe = A − k`, sold at `t = 1` at price
`pI` exactly when that is optimal (Definition 1.1). -/
noncomputable def valInsured (pI piSafe : ℝ) : ℝ :=
  P.ν * max (P.lam * pI) piSafe + (1 - P.ν) * max pI piSafe

/-- Expected utility (Definition 1.2) of a lender with screening cost `η` choosing screening `s`
and insurance `ℓ`, given prices `pI`, `pU` and fee `k`. -/
noncomputable def payoff (pI pU k η : ℝ) (s ℓ : Bool) : ℝ :=
  (if ℓ then P.valInsured pI (P.A - k) else P.valUninsured pU (if s then P.ψ else P.μ)) -
    (if s then η else 0)

/-- `(s, ℓ)` is optimal among all four choices for a lender with screening cost `η`. -/
def BestResponse (pI pU k η : ℝ) (s ℓ : Bool) : Prop :=
  ∀ s' ℓ', P.payoff pI pU k η s' ℓ' ≤ P.payoff pI pU k η s ℓ

end Params

/-- A threshold–share strategy profile with prices (p. 10, (1)): lenders with screening cost
`η ≤ eta` screen, a share `mL` of them and a share `m` of the high-cost lenders (`η > eta`)
insure; `pI`, `pU` are the secondary-market prices and `k` the insurance fee. -/
structure Profile where
  eta : ℝ
  mL : ℝ
  m : ℝ
  pI : ℝ
  pU : ℝ
  k : ℝ

namespace Params

variable (P : Params)

/-- A liquid equilibrium when loan insurance is available (Definition 1, pp. 12–13, with the
liquidity condition (2) and the sales (3), p. 10). -/
def LiquidEq (e : Profile) : Prop :=
  0 ≤ e.eta ∧ e.eta ≤ P.etaBar ∧ 0 ≤ e.mL ∧ e.mL ≤ 1 ∧ 0 ≤ e.m ∧ e.m ≤ 1 ∧
    -- Definition 1.2: each lender's choice is optimal
    (∀ η ∈ Set.Icc 0 e.eta, (e.mL < 1 → P.BestResponse e.pI e.pU e.k η true false) ∧
      (0 < e.mL → P.BestResponse e.pI e.pU e.k η true true)) ∧
    (∀ η ∈ Set.Ioc e.eta P.etaBar, (e.m < 1 → P.BestResponse e.pI e.pU e.k η false false) ∧
      (0 < e.m → P.BestResponse e.pI e.pU e.k η false true)) ∧
    -- Definition 1.3: the insurer (who pays `A` on every insured default) breaks even
    e.k * (e.mL * P.F e.eta + e.m * (1 - P.F e.eta)) =
      P.A * (e.mL * P.F e.eta * (1 - P.ψ) + e.m * (1 - P.F e.eta) * (1 - P.μ)) ∧
    -- Definition 1.3: buyers of insured loans (safe payoff `A − k`) break even
    e.pI = P.A - e.k ∧
    -- Definition 1.3 with the sales (3): buyers of uninsured loans break even
    e.pU * (P.ν * (P.F e.eta * (1 - e.mL) + (1 - P.F e.eta) * (1 - e.m)) +
        (1 - P.ν) * ((1 - P.ψ) * P.F e.eta * (1 - e.mL) +
          (1 - P.μ) * (1 - P.F e.eta) * (1 - e.m))) =
      P.ν * P.A * (P.ψ * P.F e.eta * (1 - e.mL) + P.μ * (1 - P.F e.eta) * (1 - e.m)) ∧
    -- (2): the market for uninsured loans is liquid
    P.A ≤ P.lam * e.pU

/-- Expected utility (Definition 3.3) of a lender with screening cost `η` choosing screening `s`
when loan insurance is unavailable. -/
noncomputable def payoffNoIns (pU η : ℝ) (s : Bool) : ℝ :=
  P.valUninsured pU (if s then P.ψ else P.μ) - (if s then η else 0)

/-- A liquid equilibrium when loan insurance is unavailable (Definition 3, p. 39, with (2) and the
sales (3)): lenders with cost `η ≤ eta` screen, the others do not, every choice is optimal, and
the price `pU` makes buyers break even. -/
def LiquidEqNoIns (eta pU : ℝ) : Prop :=
  0 ≤ eta ∧ eta ≤ P.etaBar ∧
    (∀ η ∈ Set.Icc 0 eta, ∀ s, P.payoffNoIns pU η s ≤ P.payoffNoIns pU η true) ∧
    (∀ η ∈ Set.Ioc eta P.etaBar, ∀ s, P.payoffNoIns pU η s ≤ P.payoffNoIns pU η false) ∧
    pU * (P.ν + (1 - P.ν) * ((1 - P.ψ) * P.F eta + (1 - P.μ) * (1 - P.F eta))) =
      P.ν * P.A * (P.ψ * P.F eta + P.μ * (1 - P.F eta)) ∧
    P.A ≤ P.lam * pU

/-- The no-insurance system (4)–(5) (p. 11): price (4) and screening threshold (5). -/
def BenchmarkFP (η₀ p₀ : ℝ) : Prop :=
  0 ≤ η₀ ∧ η₀ ≤ P.etaBar ∧ p₀ = P.price4 η₀ ∧ η₀ = (1 - P.ν) * (P.ψ - P.μ) * (P.A - p₀)

end Params

end LoanInsurance.Liquid


