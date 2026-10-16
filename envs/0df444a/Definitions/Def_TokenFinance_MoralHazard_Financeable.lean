-- Prove2me | Definitions.Def_TokenFinance_MoralHazard_Financeable
-- name    : TokenFinance_MoralHazard_Financeable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:50.253507+00:00
-- url     : https://prove2.me/theorems/10f3f150-c144-468e-bbef-d091aefb7a70
-- title:
--   §IV — standing assumptions and financeability under moral hazard by equity (17)–(18), debt (21)–(22) and optimal tokens (26)–(27)
-- statement:
--   Financing with moral hazard (§IV). With effort the demand intercept is uniform on $(0,\theta_h)$, without effort on $(0,\theta_l)$, $\theta_l<\theta_h$. Effort costs the entrepreneur $C_e$ (in value, not money). She chooses effort after the contract is signed, and effort cannot be contracted upon, so investors price the contract under effort and the contract finances the project only if the entrepreneur then prefers effort. Write $\mathrm{NPV}_h=\mathrm{NPV}(\theta_h)$ and $\mathrm{NPV}_l=\mathrm{NPV}(\theta_l)$.
--
--   1. **Standing assumptions** (pp. 26–27). $0<c<\theta_l<\theta_h$, $C_0>0$, $\mathrm{NPV}_l\le0<\mathrm{NPV}_h$ (the project has positive expected NPV only with effort) and $C_e<\mathrm{NPV}_h$.
--   2. **Equity** ((17)–(18)). With $\alpha_s=C_0/\mathbb E_{\theta_h}[\pi^m]$,
--   $$(1-\alpha_s)\,\mathbb E_{\theta_h}[\pi^m]-C_e\ \ge\ (1-\alpha_s)\,\mathbb E_{\theta_l}[\pi^m].$$
--   3. **Debt** ((21)–(22)). There is a face value $D\ge0$ with $\mathbb E_{\theta_h}[\min\{\pi^m,D\}]=C_0$ and
--   $$\mathbb E_{\theta_h}\big[\max\{\pi^m-D,0\}\big]-C_e\ \ge\ \mathbb E_{\theta_l}\big[\max\{\pi^m-D,0\}\big].$$
--   4. **Optimal tokens** ((26)–(27)). There is a pre-sale $t\in(0,(\theta_h-c)/2)$ solving condition (16) at $\theta=\theta_h$ such that, producing the monopoly quantity,
--   $$\mathbb E_{\theta_h}\big[\pi^e_t(x,q^m(x))\big]-C_e\ \ge\ \mathbb E_{\theta_l}\big[\pi^e_t(x,q^m(x))\big].$$
--
--   The contract terms $\alpha_s$, $D$, $t$ are fixed by $\theta_h$ alone (footnote 10).
--
--   **Formalization Note** The incentive constraints compare expectations of realized payoffs, with the positive part in the debt and token payoffs. When $\theta_l\le c+2\sqrt D$ (resp. $\theta_l\le c+2t$) the printed right-hand sides of (22) and (27) have a reversed integration range or a negative cube; with positive parts the no-effort profit is then $0$, which is the paper's reading ("the moral hazard problem does not arise"). The assumption $\mathrm{NPV}_h>0$ is written out: the page says the NPV is positive only with effort and exceeds $C_e$, and without it a negative $C_e$ would let equity "finance" a project with $\mathrm{NPV}_h\le0$ that no token contract can. No sign is imposed on $C_e$. The token break-even is condition (16) as printed.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 26–28 (PDF 27–29), (17)–(19); pp. 28–29 (PDF 29–30), (21)–(23); pp. 31–32 (PDF 32–33), (26)–(28), footnote 10

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.MoralHazard

/-- The standing assumptions of §IV (pp. 26–27): positive marginal cost, `c < θl < θh`, a positive
set-up cost, the project has positive expected NPV only with effort (`NPV_l ≤ 0 < NPV_h`), and
`NPV_h` exceeds the cost of effort `C_e`. -/
def MHAssumptions (c C0 Ce θl θh : ℝ) : Prop :=
  0 < c ∧ c < θl ∧ θl < θh ∧ 0 < C0 ∧ TokenFinance.Debt.npv c C0 θl ≤ 0 ∧ 0 < TokenFinance.Debt.npv c C0 θh ∧ Ce < TokenFinance.Debt.npv c C0 θh

/-- Equity financing with moral hazard, (17) + (18): investors take the share `α_s` that breaks
even under effort, and the entrepreneur then prefers to exert effort. -/
def EquityFinanceable (c C0 Ce θl θh : ℝ) : Prop :=
  (1 - TokenFinance.Debt.equityShare c C0 θh) * TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) - Ce ≥ (1 - TokenFinance.Debt.equityShare c C0 θh) * TokenFinance.Debt.expect θl (TokenFinance.Debt.pim c)

/-- Debt financing with moral hazard, (21) + (22): some face value `D ≥ 0` lets investors break
even under effort, and the entrepreneur then prefers to exert effort. -/
def DebtFinanceable (c C0 Ce θl θh : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0 ∧
    TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) - Ce ≥ TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D)

/-- Optimal token financing with moral hazard, (26) + (27): some pre-sale `t ∈ (0, (θh − c)/2)`
solves the break-even condition (16) at `θh`, and the entrepreneur, producing the monopoly
quantity, then prefers to exert effort. -/
def TokenFinanceable (c C0 Ce θl θh : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < (θh - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θh t ∧
    TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) - Ce ≥ TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x))

end TokenFinance.MoralHazard


