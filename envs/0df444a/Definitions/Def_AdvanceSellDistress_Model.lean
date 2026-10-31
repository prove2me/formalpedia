-- Prove2me | Definitions.Def_AdvanceSellDistress_Model
-- name    : AdvanceSellDistress_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:47.84522+00:00
-- url     : https://prove2.me/theorems/fe8d89d0-6758-443b-aa55-a2eb95ef08dc
-- title:
--   Advance selling under financial distress: parameters, bank financing subgame, and the hybrid coupon scheme H
-- statement:
--   This module fixes the model of Papanastasiou, Xiao and Yang (§3.1 and §4.2.3).
--
--   **Parameters.** A small firm needs funding $I\ge0$. Its later effort $e\in[0,1]$ costs $ae^2$ ($a>0$) and succeeds with probability $e$. With probability $1-\beta$ the firm cannot operate in the repayment period (no revenue, nothing repaid); $\beta\in(0,1]$. An inner segment of mass $1$ values the service at $v\ge1$, an outer segment of mass $m_o>0$ at $1$; after success every consumer values the service, after no success only a fraction $\lambda\in(0,1)$ does. Write $v_m=\max\{1+m_o,v\}$,
--   $$I_l=\beta\lambda v_m,\qquad I_h=I_l+\frac{\beta(1-\lambda)^2v_m^2}{8a},\qquad I_{\max}=\beta\Big[\lambda v_m+\frac{(1-\lambda)^2v_m^2}{4a}\Big].$$
--   The standing assumptions are **Assumption 1** $a\ge(1-\lambda)v_m/2$ and **Assumption 2** $I<I_{\max}$.
--
--   **Revenues.** Without coupons, at regular price $p_r$ the revenue in a state with valuation probability $\lambda_z$ is $\lambda_z\,(p_r\mathbf 1[p_r\le v]+p_r m_o\mathbf 1[p_r\le1])$. When every inner consumer holds a coupon $(p_a,p_s)$ it is $\lambda_z\,(p_s\mathbf 1[p_s\le v]+p_r m_o\mathbf 1[p_r\le1])$.
--
--   **Financing subgame.** For revenues $S_s$ (success) and $S_n$ (no success), a loan $L$ and a face value $D\ge0$:
--   1. the firm's payoff is $U(e;D)=e(S_s-D)^++(1-e)(S_n-D)^+-ae^2$, and its effort is any maximizer of $U(\cdot;D)$ on $[0,1]$;
--   2. $D$ breaks even if $L=\beta[e\min(S_s,D)+(1-e)\min(S_n,D)]$ at that effort;
--   3. the competitive bank charges the least break-even face value, and the loan is granted iff one exists;
--   4. the firm's expected profit with advance revenue $p_a$ and loan $L=\max(I-p_a,0)$ is $\max(p_a-I,0)+\beta U(e;D)$.
--
--   **Bank-only benchmark.** Loan $I$, revenues $v_m$ and $\lambda v_m$. The regular price is $p^*_{rB}=1$ if $v\le1+m_o$ and $v$ otherwise. The bank-only profit is $\pi_B=\beta U(e_B;D_B)$ and a waiting inner consumer's expected surplus is $U_B=\beta[e_B+(1-e_B)\lambda](v-p^*_{rB})$. If no face value breaks even, the firm goes bankrupt and $\pi_B=U_B=0$.
--
--   **Scheme H.** Discount coupons $(p_a,p_s)$ are sold with an all-or-nothing clause. If all inner consumers buy, the firm raises $p_a$, borrows $\max(I-p_a,0)$, and its revenues are $p_s+m_o$ and $\lambda(p_s+m_o)$ (regular price $1$). A buyer's expected utility is $E[u_{bb}]=-p_a+\beta[e+(1-e)\lambda](v-p_s)^+$. Under the clause any deviation sends the game to the bank-only benchmark, so $E[u_{bw}]=E[u_{wb}]=E[u_{ww}]=U_B$. Consumers purchase iff Lemma A.1 holds:
--   $$E[u_{bb}]\ge E[u_{bw}]\quad\text{and}\quad\big(E[u_{wb}]>E[u_{ww}]\ \text{or}\ E[u_{bb}]\ge E[u_{ww}]\big).$$
--   A **feasible H plan** with effort $e$ and profit $\pi$ is a plan with $p_s\in[0,1]$, $p_a\in\mathbb R$, whose all-buy financing is secured with effort $e$ and profit $\pi$, and which the consumers purchase.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** `lam` is $\lambda$. Effort is a best response on `Set.Icc 0 1` and the face value the **least** break-even one (`IsLeast`); no closed form is used in the model. The deviation utilities equal $U_B$ because of the all-or-nothing clause, and the $k\to\infty$ limit of footnote 3 then plays no role. Lemma A.1's weak inequalities are used. The revenues entering the financing subgame are those at the revenue-maximizing regular price, which the theorems prove. Every square root in the statements has a radicand that the statement's hypotheses make nonnegative.
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, §3.1 pp.5–7 (PDF 6–8): parameters, Assumptions 1–2, I_l, I_h; proof of Proposition 1 eqs. (1)–(7), pp.34–35 (PDF 35–36); §4.1.3 p.12 (PDF 13) coupons; §4.2.3 p.19 (PDF 20) scheme H; Lemma A.1 p.28 (PDF 29); proof of Proposition A.7 (127)–(131), pp.78–79 (PDF 79–80)

import Mathlib

namespace AdvanceSellDistress

/-- The primitive parameters of the model of Papanastasiou–Xiao–Yang, *Advance Selling to Ease
Financial Distress*, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, §3.1,
pp. 5–7 (PDF 6–8):

* `a` — effort cost coefficient, `c(e) = a e²`;
* `β` — probability that the firm is able to operate in the repayment period;
* `lam` — `λ = λ_n`, the probability that a consumer values the service after an unsuccessful
  effort outcome (`λ_s = 1` after success);
* `v` — valuation of the inner segment (mass `m_i = 1`); the outer segment values the service at `1`;
* `mo` — mass of the outer segment;
* `I` — the funding need.

**Formalization Note.** `lam` stands for the paper's `λ`. The standing assumptions are collected in
`Params.Standing`. -/
structure Params where
  /-- effort cost coefficient `a` (`c(e) = a e²`) -/
  a : ℝ
  /-- probability `β` that the firm can operate in the repayment period -/
  β : ℝ
  /-- `λ = λ_n`, valuation probability after an unsuccessful effort outcome -/
  lam : ℝ
  /-- inner-segment valuation `v` -/
  v : ℝ
  /-- outer-segment mass `m_o` -/
  mo : ℝ
  /-- funding need `I` -/
  I : ℝ

namespace Params

variable (P : Params)

/-- `v_m = max{(m_i + m_o) v_o, m_i v_i} = max{1 + m_o, v}`, the maximum achievable revenue in the
repayment period (Management Science 2025, doi:10.1287/mnsc.2020.03904, §3.1, p. 7, PDF 8). -/
noncomputable def vm : ℝ := max (1 + P.mo) P.v

/-- The low-distress threshold `I_l = β λ v_m` (Management Science 2025,
doi:10.1287/mnsc.2020.03904, §3.2, p. 7, PDF 8). -/
noncomputable def Il : ℝ := P.β * P.lam * P.vm

/-- The high-distress threshold `I_h = I_l + β (1 − λ)² v_m² / (8a)` (Management Science 2025,
doi:10.1287/mnsc.2020.03904, §3.2, p. 7, PDF 8). -/
noncomputable def Ih : ℝ := P.Il + P.β * (1 - P.lam) ^ 2 * P.vm ^ 2 / (8 * P.a)

/-- `I_max = β [λ v_m + (1 − λ)² v_m² / (4a)]` of Assumption 2 (Management Science 2025,
doi:10.1287/mnsc.2020.03904, §3.1, p. 7, PDF 8). -/
noncomputable def Imax : ℝ := P.β * (P.lam * P.vm + (1 - P.lam) ^ 2 * P.vm ^ 2 / (4 * P.a))

/-- The standing assumptions of the model (Management Science 2025, doi:10.1287/mnsc.2020.03904,
§3.1, pp. 6–7, PDF 7–8): `a > 0`, `β ∈ (0, 1]`, `λ ∈ (0, 1)`, `v ≥ 1`, `m_o > 0`, `I ≥ 0`,
**Assumption 1** `a ≥ (1 − λ) v_m / 2` and **Assumption 2** `I < I_max`.

**Formalization Note.** The paper writes `1 − β ∈ [0, 1]`; `β > 0` is added because the paper
divides by `β` (`I/β`, `r = 1/β − 1`), and `I_l < I` forces it in every result of the paper that
is formalized here. -/
structure Standing : Prop where
  a_pos : 0 < P.a
  β_pos : 0 < P.β
  β_le_one : P.β ≤ 1
  lam_pos : 0 < P.lam
  lam_lt_one : P.lam < 1
  one_le_v : 1 ≤ P.v
  mo_pos : 0 < P.mo
  I_nonneg : 0 ≤ P.I
  assumption1 : (1 - P.lam) * P.vm / 2 ≤ P.a
  assumption2 : P.I < P.Imax

/-! ### Repayment-period revenues -/

/-- Repayment-period sales revenue **without coupons** at regular price `p_r`, in a state in which
each consumer values the service with probability `lz` (`lz = λ_s = 1` after success,
`lz = λ_n = λ` after no success). With a continuum of consumers, mass `lz` of the inner segment
values the service at `v` and mass `lz · m_o` of the outer segment at `1`; a consumer buys iff her
valuation is at least the price (Management Science 2025, doi:10.1287/mnsc.2020.03904, §3.1,
pp. 6–7, and proof of Proposition 1, p. 34, PDF 35). -/
noncomputable def bankRevenue (lz pr : ℝ) : ℝ :=
  lz * ((if pr ≤ P.v then pr else 0) + (if pr ≤ 1 then pr * P.mo else 0))

/-- Repayment-period sales revenue when **every inner consumer holds a coupon** `(p_a, p_s)` and the
outer consumers pay the regular price `p_r` (§4.1.3, p. 12, PDF 13): coupon holders who value the
service pay `p_s`, outer consumers who value it buy iff `p_r ≤ 1` (Management Science 2025,
doi:10.1287/mnsc.2020.03904). The paper requires `p_r ≥ p_s`. -/
noncomputable def couponRevenue (lz ps pr : ℝ) : ℝ :=
  lz * ((if ps ≤ P.v then ps else 0) + (if pr ≤ 1 then pr * P.mo else 0))

/-! ### The financing subgame (proof of Proposition 1, eqs. (1)–(7), pp. 34–35) -/

/-- The firm's repayment-period payoff, conditional on being able to operate, from effort `e` when
it owes face value `D` and its revenue is `S_s` after success (probability `e`) and `S_n` after no
success, eq. (1) of the proof of Proposition 1 (Management Science 2025,
doi:10.1287/mnsc.2020.03904, p. 34, PDF 35):
`U(e; D) = e (S_s − D)⁺ + (1 − e)(S_n − D)⁺ − a e²` (limited liability). -/
noncomputable def effortPayoff (Ss Sn D e : ℝ) : ℝ :=
  e * max (Ss - D) 0 + (1 - e) * max (Sn - D) 0 - P.a * e ^ 2

/-- `e` is a best-response effort to the face value `D`: it maximizes `U(·; D)` over `[0, 1]`
(proof of Proposition 1, eqs. (1)–(3), p. 34, PDF 35; Management Science 2025,
doi:10.1287/mnsc.2020.03904).

**Formalization Note.** Effort is defined as the maximizer on `Set.Icc 0 1`, not by the closed
form (3). -/
def IsEffortBR (Ss Sn D e : ℝ) : Prop :=
  e ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ e' ∈ Set.Icc (0 : ℝ) 1, P.effortPayoff Ss Sn D e' ≤ P.effortPayoff Ss Sn D e

/-- Fair pricing, eq. (4) of the proof of Proposition 1 (p. 34, PDF 35; Management Science 2025,
doi:10.1287/mnsc.2020.03904): a loan `L` with face value `D = L (1 + r) ≥ 0` breaks even for the
bank iff, at the firm's best-response effort `e`, the expected repayment equals `L`:
`L = β [e · min(S_s, D) + (1 − e) · min(S_n, D)]` (risk-free rate zero, repayment only if the firm
operates, limited liability). -/
def BreaksEven (Ss Sn L D : ℝ) : Prop :=
  0 ≤ D ∧ ∃ e, P.IsEffortBR Ss Sn D e ∧ L = P.β * (e * min Ss D + (1 - e) * min Sn D)

/-- The outcome of the financing subgame for a loan `L`: the competitive bank charges the **least**
break-even face value `D` ("the smaller root due to the competitiveness of the bank credit
market", proof of Proposition 1, p. 35, PDF 36) and the firm exerts its best-response effort `e`
to `D` (Management Science 2025, doi:10.1287/mnsc.2020.03904). The interest rate is
`r = D / L − 1`. The loan is granted iff some face value breaks even.

**Formalization Note.** When `L = 0` the least break-even face value is `0` (no loan). -/
def FinancingOutcome (Ss Sn L D e : ℝ) : Prop :=
  IsLeast {D' | P.BreaksEven Ss Sn L D'} D ∧ P.IsEffortBR Ss Sn D e

/-- The firm's expected profit when it raises `p_a` in advance (`p_a = 0` without advance
selling), borrows `L = max(I − p_a, 0)` at face value `D` and exerts effort `e`:
`max(p_a − I, 0) + β · U(e; D)` (Management Science 2025, doi:10.1287/mnsc.2020.03904; this is
Proposition 1's `β[−a e² + …] − I` and Lemma A.5's `β[…] + p_a − I`, pp. 8, 32–35). -/
noncomputable def firmProfit (Ss Sn pa D e : ℝ) : ℝ :=
  max (pa - P.I) 0 + P.β * P.effortPayoff Ss Sn D e

/-! ### The bank-only benchmark (§3, Proposition 1) -/

/-- The bank-only financing outcome: loan `I`, revenues `S_s = v_m`, `S_n = λ v_m` at the
revenue-maximizing regular price (Management Science 2025, doi:10.1287/mnsc.2020.03904,
Proposition 1 and its proof, pp. 7–8, 34–35).

**Formalization Note.** The revenues are those at the revenue-maximizing regular price; that this
price is revenue-maximizing is the price clause of `AdvanceSellDistress.proposition_1`. -/
def BankOutcome (D e : ℝ) : Prop :=
  P.FinancingOutcome P.vm (P.lam * P.vm) P.I D e

/-- The bank-only regular price: `1` if `v ≤ 1 + m_o`, else `v` (proof of Proposition A.7, p. 78,
PDF 79: "Since v ≤ 1 + mo, the firm would set the regular selling price equal to p*_rB = 1";
Management Science 2025, doi:10.1287/mnsc.2020.03904).

**Formalization Note.** At the tie `v = 1 + m_o` both prices maximize revenue; Proposition 1
prints `v` there, the proof of Proposition A.7 uses `1`. The tie-break of A.7 is used. -/
noncomputable def pB : ℝ := if P.v ≤ 1 + P.mo then 1 else P.v

/-- The expected surplus of an inner consumer who waits and buys at the bank-only regular price,
given bank-only effort `e`: `β [e + (1 − e) λ] (v − p*_rB)⁺` (proof of Proposition A.7, p. 78,
PDF 79; Management Science 2025, doi:10.1287/mnsc.2020.03904). -/
noncomputable def waitSurplus (e : ℝ) : ℝ :=
  P.β * (e + (1 - e) * P.lam) * max (P.v - P.pB) 0

/-- The bank-only benchmark: the firm's profit `π_B` and a waiting inner consumer's expected
surplus `U_B`. Either the bank lends (least break-even face value, best-response effort `e_B`),
and then `π_B = β U(e_B; D_B)` and `U_B = β [e_B + (1 − e_B) λ](v − p*_rB)`, or no face value
breaks even, the firm goes bankrupt and `π_B = U_B = 0` (Management Science 2025,
doi:10.1287/mnsc.2020.03904, Proposition 1, pp. 7–8; p. 78). -/
def BankBenchmark (πB uB : ℝ) : Prop :=
  (∃ D e, P.BankOutcome D e ∧ πB = P.firmProfit P.vm (P.lam * P.vm) 0 D e ∧
      uB = P.waitSurplus e) ∨
    ((¬ ∃ D, P.BreaksEven P.vm (P.lam * P.vm) P.I D) ∧ πB = 0 ∧ uB = 0)

/-! ### The hybrid scheme "H": coupons with an all-or-nothing clause (§4.2.3, p. 19) -/

/-- The all-buy financing outcome of a coupon plan `(p_a, p_s)` under scheme "H": every inner
consumer (mass 1) has bought a coupon, so the firm raises `p_a`, borrows `L = max(I − p_a, 0)`, and
its revenues at the revenue-maximizing regular price `p_r = 1` are `S_s = p_s + m_o`,
`S_n = λ (p_s + m_o)` (Management Science 2025, doi:10.1287/mnsc.2020.03904, Lemma A.5,
pp. 32–33; proof of Proposition A.7, p. 78).

**Formalization Note.** The revenues are those at the revenue-maximizing regular price `1`, proved
in clause (0) of `AdvanceSellDistress.proposition_10`; they presuppose `p_s ≤ v`. -/
def HAllBuyOutcome (pa ps D e : ℝ) : Prop :=
  P.FinancingOutcome (ps + P.mo) (P.lam * (ps + P.mo)) (max (P.I - pa) 0) D e

/-- `E[u_bb]`: the expected utility of an inner consumer who buys the coupon `(p_a, p_s)` when all
other inner consumers buy, given the firm's all-buy effort `e`:
`−p_a + β [e + (1 − e) λ] (v − p_s)⁺` (eqs. (129), (139), pp. 78, 82; Management Science 2025,
doi:10.1287/mnsc.2020.03904). -/
noncomputable def ubb (pa ps e : ℝ) : ℝ :=
  -pa + P.β * (e + (1 - e) * P.lam) * max (P.v - ps) 0

/-- The deviation utilities `E[u_bw]`, `E[u_wb]`, `E[u_ww]` under scheme "H", as functions of the
bank-only waiting surplus `U_B`: all three equal `U_B` (Management Science 2025,
doi:10.1287/mnsc.2020.03904, proof of Proposition A.7, p. 78, "we have E[ubw] = E[uww]").

**Formalization Note.** With the all-or-nothing clause, the coupon campaign is cancelled and
refunded unless *all* inner consumers buy. A consumer who waits while the others buy (`u_bw`),
or who buys while the others wait (`u_wb`), or who waits with everyone (`u_ww`) therefore ends
up in the bank-only benchmark and gets `U_B`. The `k → ∞` limit of footnote 3 has no effect. -/
def hDeviationUtility (uB : ℝ) : ℝ := uB

/-- The purchasing-equilibrium condition of Lemma A.1 (p. 28, PDF 29; Management Science 2025,
doi:10.1287/mnsc.2020.03904): inner consumers purchase in advance iff
(1) `E[u_bb] ≥ E[u_bw]` and (2) `E[u_wb] > E[u_ww]` or `E[u_bb] ≥ E[u_ww]`.

**Formalization Note.** Lemma A.1's weak inequalities are used (p. 9 says "lower"). -/
def LemmaA1Cond (ubb ubw uwb uww : ℝ) : Prop :=
  ubw ≤ ubb ∧ (uww < uwb ∨ uww ≤ ubb)

/-- Under scheme "H", the inner consumers purchase the coupon `(p_a, p_s)` (given the firm's
all-buy effort `e`): Lemma A.1's condition with `E[u_bb] = ubb p_a p_s e` and the deviation
utilities of the all-or-nothing clause, all equal to the bank-only waiting surplus `U_B`
(Management Science 2025, doi:10.1287/mnsc.2020.03904, pp. 28, 78). -/
def HPurchase (pa ps e : ℝ) : Prop :=
  ∃ πB uB, P.BankBenchmark πB uB ∧
    LemmaA1Cond (P.ubb pa ps e) (hDeviationUtility uB) (hDeviationUtility uB)
      (hDeviationUtility uB)

/-- A **feasible plan of scheme "H"** with effort `e` and expected profit `π`: the coupon plan
`(p_a, p_s)` has `p_s ∈ [0, 1]`, its all-buy financing is secured (least break-even face value
`D` exists) with best-response effort `e`, `π` is the firm's resulting expected profit, and the
inner consumers purchase (Lemma A.1) (Management Science 2025, doi:10.1287/mnsc.2020.03904,
§4.2.3, p. 19; Lemma A.5, pp. 32–33; proof of Proposition A.7, (127)–(131), pp. 78–79).

**Formalization Note.** Plans range over `p_a ∈ ℝ`, `p_s ∈ [0, 1]` (the domain of (131)); the
regular price is the revenue-maximizing `p_r = 1`. The firm's equilibrium choice is optimality over
feasible plans and the bank-only option; it is not defined by a formula. -/
def HPlan (pa ps e π : ℝ) : Prop :=
  ps ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ D, P.HAllBuyOutcome pa ps D e ∧
      π = P.firmProfit (ps + P.mo) (P.lam * (ps + P.mo)) pa D e ∧ P.HPurchase pa ps e

end Params

end AdvanceSellDistress


