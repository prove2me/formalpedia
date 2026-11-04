-- Prove2me | Definitions.Def_PerishBaseStock_Outdating_Heuristic
-- name    : PerishBaseStock_Outdating_Heuristic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:15.139507+00:00
-- url     : https://prove2.me/theorems/ca432b86-f493-4105-82e2-b008ec35166e
-- title:
--   (4), (9) and App. B.3 — the heuristic cost $\widetilde C_\theta$, its minimizers, the lower support $\underline D$, $S^0$ and $\min_{0\le S\le m\underline D}$
-- statement:
--   This file defines the heuristic base-stock level of Bu, Gong and Chao and the quantities of the large-outdating-cost analysis (§3.3 and Appendix B.3).
--
--   **Heuristic cost.** For $S\ge 0$ write $G(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]$ for the newsvendor cost and
--   $$\widetilde C_\theta(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big].\tag{4}$$
--   A level $\widetilde S_\theta\ge 0$ is a *heuristic level* if it minimizes $\widetilde C_\theta$ over $[0,\infty)$. The *least* heuristic level is the infimum of all such minimizers.
--
--   **Lower support and $S^0$.** With $F(x)=\mathbb P(D\le x)$, the lower support of demand is $\underline D=\inf\{x:F(x)>0\}$ (p. 15), and
--   $$S^0=\sup\Big\{S\ge 0:\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big]=0\Big\}.$$
--   Finally $\min_{0\le S\le m\underline D}G(S)$ is the best newsvendor cost among levels at most $m\underline D$.
--
--   The heuristic level is the policy whose optimality gap Theorem 4 controls; $\underline D$, $S^0$ and the restricted minimum are the objects of the proof in Appendix B.3.
--
--   **Formalization Note** $\mathbb E[(S-D)^+]$, $\mathbb E[(D-S)^+]$ and $\mathbb E[(S-\sum_{i=1}^mD_i)^+]$ are the published `expectedHolding`/`backorderCost` of `LostSalesOrderUpTo.Asymptotic.Backorder`, with `leadTimeLaw P (m - 1)` the law of $D_1+\dots+D_m$; all three integrands are integrable under the demand assumptions, so the Bochner integrals are the true expectations. The least minimizer is an infimum in $\mathbb R_{\ge0}$ over a set that is nonempty ($\widetilde C_\theta$ is continuous and coercive); $\underline D$ is a real infimum over a set that is nonempty and bounded below by $0$; $S^0$ is a real supremum over a set that is nonempty (it contains $0$) and bounded above (the expectation exceeds $S-m\mathbb E[D]$); the restricted minimum is a real infimum over the image of a nonempty set ($S=0$) of nonnegative values. None of these four therefore takes Lean's default value.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 10, (4); p. 15, (9) and the definition of D̲; p. ec6, App. B.3 (S⁰, EC.16)

import Definitions.Def_PerishBaseStock_Outdating_Model

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Outdating

/-- The newsvendor cost `hE[(S - D)^+] + pE[(D - S)^+]`. -/
def nvCost (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.p S

/-- `E[(S - ∑_{i=1}^m D_i)^+]`; `leadTimeLaw P (m - 1)` is the law of `D_1 + ⋯ + D_m`. -/
def excessOverLifetimeDemand (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.expectedHolding
    (LostSalesOrderUpTo.Asymptotic.leadTimeLaw P (c.m - 1)) S

/-- The heuristic cost (4), p. 10:
`C̃_θ(S) = hE[(S - D)^+] + pE[(D - S)^+] + (θ/m) E[(S - ∑_{i=1}^m D_i)^+]`. -/
def heurCost (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) (S : ℝ≥0) : ℝ :=
  nvCost P c S + ((θ : ℝ) / (c.m : ℝ)) * excessOverLifetimeDemand P c S

/-- `S̃` is a minimizer of `C̃_θ` over `[0, +∞)` (p. 10). -/
def IsHeurMin (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) (S : ℝ≥0) : Prop :=
  ∀ S' : ℝ≥0, heurCost P c θ S ≤ heurCost P c θ S'

/-- The least minimizer of `C̃_θ` over `[0, +∞)` (the minimizer set is nonempty and closed). -/
def leastHeurMin (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) : ℝ≥0 :=
  sInf {S : ℝ≥0 | IsHeurMin P c θ S}

/-- The distribution function `F(x) = P(D ≤ x)` of the one-period demand, for real `x`. -/
def cdf (P : CappedBaseStock.DemandLaw) (x : ℝ) : ℝ≥0∞ :=
  P.law {d : ℝ≥0 | (d : ℝ) ≤ x}

/-- The lower support `D̲ = inf{x : F(x) > 0}` (p. 15). The set is nonempty and bounded
below by `0`, so the real infimum is the paper's. -/
def lowerSupport (P : CappedBaseStock.DemandLaw) : ℝ :=
  sInf {x : ℝ | 0 < cdf P x}

/-- `S⁰ = sup{S ≥ 0 : E[(S - ∑_{i=1}^m D_i)^+] = 0}` (p. ec6). -/
def sZero (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ :=
  sSup ((fun S : ℝ≥0 => (S : ℝ)) '' {S : ℝ≥0 | excessOverLifetimeDemand P c S = 0})

/-- `min_{0 ≤ S ≤ mD̲} {hE[(S - D)^+] + pE[(D - S)^+]}`, as a real infimum over a set that
contains `S = 0` and is bounded below by `0`. -/
def nvMinBelow (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ :=
  sInf (nvCost P c '' {S : ℝ≥0 | (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P})

end PerishBaseStock.Outdating


