-- Prove2me | Definitions.Def_QFlexSC_MCOpt_FOLFC
-- name    : QFlexSC_MCOpt_FOLFC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:03.070505+00:00
-- url     : https://prove2.me/theorems/098a0219-27de-40fb-be42-0712fd03ae0c
-- title:
--   Program (F-OLFC), p. 96, (17)–(20), its relaxation and the solution (30)–(31) of Appendix 1
-- statement:
--   Fix a period $t$ with data $I(t-1)$, the previous replenishment schedule $r(t-1)$, the current release schedule $f(t)$, a convex stock cost $G$ and a horizon $h$. The open-loop program **(F-OLFC)** of p. 96 chooses the schedule $r(t) = (r_0(t), \dots, r_h(t))$ and the planned purchases $(r_0(t), r_0(t+1), \dots, r_0(t+h))$ to
--   $$\min \sum_{j=0}^{h} G\big(I(t+j)\big)$$
--   subject to, for $j = 0, \dots, h$,
--   1. (17) $I(t+j) = I(t+j-1) + r_0(t+j) - (1 + A^{out}_j) f_j(t)$;
--   2. (18) $I(t+j) \ge 0$;
--   3. (19) $(1 - \omega^{in}_{j+1})\, r_{j+1}(t-1) \le r_j(t) \le (1 + \alpha^{in}_{j+1})\, r_{j+1}(t-1)$;
--   4. (20) $(1 - \Omega^{in}_j)\, r_j(t) \le r_0(t+j) \le (1 + A^{in}_j)\, r_j(t)$.
--
--   The **relaxed program** of Appendix 1 keeps (17), (18) and the lower bounds of (19) and (20) only. Its solution (30)–(31) is
--   $$r_0^*(t+j) = \max\big\{(1 + A^{out}_j) f_j(t) - \bar l_j(t),\ (1 - \Omega^{in}_{j+1})\, r_{j+1}(t-1)\big\},$$
--   with $\bar l_0(t) = I(t-1)$ and $\bar l_{j+1}(t) = \bar l_j(t) + r_0^*(t+j) - (1 + A^{out}_j) f_j(t)$.
--
--   This module defines the stock path (17), the feasible sets of (F-OLFC) and of the relaxed program, the objective, and $r_0^*$, $\bar l$.
--
--   **Formalization Note** The paper prints (19) "for $j = 0, \dots, h-1$". Here (19) is imposed for $j = 0, \dots, h$: (21) and (30) both use $r_{h+1}(t-1)$, (19) for $j \le h$ is the contract (7) restricted to the horizon, and with the printed range Proposition 1's optimality claim fails (a one-period counterexample with $h = 0$ is in the mission description). The planned purchase $r_0(t+0)$ is a decision variable `p 0`, tied to $r_0(t)$ by (20) at $j = 0$ ($A_0 = \Omega_0 = 0$). Decision variables are arbitrary real sequences; only indices $j \le h$ enter. The stock is the closed form $I(t+j) = I(t-1) + \sum_{q=0}^{j} \big(r_0(t+q) - (1 + A^{out}_q) f_q(t)\big)$ of (17).
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 96, (17)–(20); Appendix 1, pp. 107–108, (30)–(31)

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.MCOpt

/-- The projected stock `I(t + j)` of program (F-OLFC), by (17):
`I(t+j) = I(t-1) + ∑_{q=0}^{j} (r_0(t+q) - (1 + A^out_q) f_q(t))`, where `Iprev = I(t-1)`,
`f = f(t)` and `p q = r_0(t+q)`. -/
noncomputable def stock (P : QFlexSC.ZeroInv.QFParams) (Iprev : ℝ) (f p : ℕ → ℝ) (j : ℕ) : ℝ :=
  Iprev + ∑ q ∈ Finset.range (j+1), (p q - (1 + QFlexSC.ZeroInv.Acum P.αout q) * f q)

/-- Feasibility for program (F-OLFC) (17)–(20) at one period, with horizon `h`, data
`Iprev = I(t-1)`, `rprev = r(t-1)`, `f = f(t)`, decision `x = r(t)` (only `x j`, `j ≤ h`, matter)
and planned purchases `p j = r_0(t+j)`, `j = 0, …, h`. For every `j ≤ h`: (18) stock nonnegative,
(19) the input IR constraint (imposed for `j = 0, …, h`), and (20) the CF bounds. -/
def Feasible (P : QFlexSC.ZeroInv.QFParams) (h : ℕ) (Iprev : ℝ) (rprev f x p : ℕ → ℝ) : Prop :=
  ∀ j, j ≤ h →
    0 ≤ stock P Iprev f p j ∧
    ((1 - P.ωin (j+1)) * rprev (j+1) ≤ x j ∧ x j ≤ (1 + P.αin (j+1)) * rprev (j+1)) ∧
    ((1 - QFlexSC.ZeroInv.Ωcum P.ωin j) * x j ≤ p j ∧ p j ≤ (1 + QFlexSC.ZeroInv.Acum P.αin j) * x j)

/-- Feasibility for the relaxation of (F-OLFC) used in Appendix 1: (18) and the lower bounds of
(19) and (20) only, for every `j ≤ h`. -/
def RelaxedFeasible (P : QFlexSC.ZeroInv.QFParams) (h : ℕ) (Iprev : ℝ) (rprev f x p : ℕ → ℝ) : Prop :=
  ∀ j, j ≤ h →
    0 ≤ stock P Iprev f p j ∧
    (1 - P.ωin (j+1)) * rprev (j+1) ≤ x j ∧
    (1 - QFlexSC.ZeroInv.Ωcum P.ωin j) * x j ≤ p j

/-- The objective of (F-OLFC): `∑_{j=0}^{h} G(I(t+j))`. -/
noncomputable def objective (G : ℝ → ℝ) (P : QFlexSC.ZeroInv.QFParams) (h : ℕ) (Iprev : ℝ) (f p : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (h+1), G (stock P Iprev f p j)

/-- `l̄_j(t)` of (31): `l̄_0(t) = I(t-1)` and
`l̄_{j+1}(t) = l̄_j(t) + r_0^*(t+j) - (1 + A^out_j) f_j(t)`, with `r_0^*(t+j)` given by (30). -/
noncomputable def lbar (P : QFlexSC.ZeroInv.QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ) : ℕ → ℝ
  | 0 => Iprev
  | j+1 => lbar P Iprev rprev f j
      + max ((1 + QFlexSC.ZeroInv.Acum P.αout j) * f j - lbar P Iprev rprev f j)
            ((1 - QFlexSC.ZeroInv.Ωcum P.ωin (j+1)) * rprev (j+1))
      - (1 + QFlexSC.ZeroInv.Acum P.αout j) * f j

/-- `r_0^*(t+j)` of (30):
`max{(1 + A^out_j) f_j(t) - l̄_j(t), (1 - Ω^in_{j+1}) r_{j+1}(t-1)}`. -/
noncomputable def pStar (P : QFlexSC.ZeroInv.QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ) (j : ℕ) : ℝ :=
  max ((1 + QFlexSC.ZeroInv.Acum P.αout j) * f j - lbar P Iprev rprev f j)
      ((1 - QFlexSC.ZeroInv.Ωcum P.ωin (j+1)) * rprev (j+1))

end QFlexSC.MCOpt


