-- Prove2me | Definitions.Def_PerishBaseStock_Lifo_Heuristic
-- name    : PerishBaseStock_Lifo_Heuristic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:45.622745+00:00
-- url     : https://prove2.me/theorems/7e3d81e2-8d2b-4394-95ad-21bc6b33912e
-- title:
--   (4), (11), (12) — $\widetilde C$, $\hat C_L$, $\hat C_U$, the levels $\widetilde S$, $\hat S$, and $S^{NP}$
-- statement:
--   This file defines the explicit cost functions and heuristic base-stock levels of the LIFO analysis of Bu, Gong and Chao, on top of the LIFO model of this mission. Let $D, D_1, \dots, D_m$ be i.i.d. demands and $S\ge 0$.
--
--   1. The bounds of Lemma 3, (11) and (12):
--   $$\hat C_L(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E[(S-\max\{D_1,\dots,D_m\})^+],$$
--   $$\hat C_U(S)=\Big(h+\frac{\theta}{m}\Big)\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+].$$
--   2. $\hat S$ is a *minimizer* of $(\hat C_L(S)+\hat C_U(S))/2$ over $[0,\infty)$ (p. 16).
--   3. The function (4)
--   $$\widetilde C(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\frac{\theta}{m}\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big],$$
--   and $\widetilde S$ is a minimizer of $\widetilde C$ over $[0,\infty)$ (p. 10).
--   4. $S^{NP}=F^{-1}(p/(p+h))$, the newsvendor level, with $F^{-1}(x)=\inf\{y:F(y)\ge x\}$.
--
--   $\hat S$ is the base-stock level whose performance Theorem 5 guarantees; $\widetilde C(\widetilde S)$ is the lower bound on the optimal cost of Proposition 2.
--
--   **Formalization Note** The law of $\max\{D_1,\dots,D_m\}$ is `maxLaw P (m - 1)`, the image of the i.i.d. path law under $d\mapsto\max_{i<m}d_i$, in the same convention as the published `leadTimeLaw P (m - 1)` (the law of $D_1+\dots+D_m$). The expectations are the published `expectedHolding` and `expectedShortfall`; all integrands are bounded by $S$ or by $D$, so no Bochner integral defaults to zero. "A minimizer" is a predicate, and the statements of the mission quantify over every minimizer.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 10, (4) and S^NP; p. 8, F^{-1}; p. 16, (11), (12) and Ŝ

import Definitions.Def_PerishBaseStock_Lifo_Model

/-!
# The bounds `Ĉ_L`, `Ĉ_U`, the heuristic levels `Ŝ`, `S̃` (Bu, Gong & Chao, (4), (11), (12))

All expectations are Bochner integrals of bounded or integrable functions
(`(S - X)⁺ ≤ S`; `(D - S)⁺ ≤ D` with `E[D] < ∞`), so none of them is a junk zero.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifo

open LostSalesOrderUpTo.Asymptotic

/-- The law of `max{D_1, …, D_{k+1}}` (the analogue of `leadTimeLaw P k`, the law of
`D_1 + ⋯ + D_{k+1}`). At `k = m - 1` it is the law of `max{D_1, …, D_m}`. -/
def maxLaw (P : CappedBaseStock.DemandLaw) (k : ℕ) : Measure ℝ≥0 :=
  Measure.map (fun d : CappedBaseStock.DemandPath => (Finset.range (k + 1)).sup d)
    (CappedBaseStock.demandPathLaw P)

/-- `S^NP = F^{-1}(p/(p+h))`, the newsvendor level. -/
def snp (P : CappedBaseStock.DemandLaw) (c : Params) : ℝ≥0 :=
  newsvendorLevel P.law c.h c.p

/-- (11): `Ĉ_L(S) = hE[(S-D)⁺] + pE[(D-S)⁺] + (θ/m)E[(S - max{D_1,…,D_m})⁺]`. -/
def hatCL (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  backorderCost P.law c.h c.p S + c.θ / c.m * expectedHolding (maxLaw P (c.m - 1)) S

/-- (12): `Ĉ_U(S) = (h + θ/m)E[(S-D)⁺] + pE[(D-S)⁺]`. -/
def hatCU (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  (c.h + c.θ / c.m) * expectedHolding P.law S + c.p * expectedShortfall P.law S

/-- `(Ĉ_L(S) + Ĉ_U(S))/2`, the function whose minimizer is `Ŝ`. -/
def hatObjective (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  (hatCL P c S + hatCU P c S) / 2

/-- `Ŝ` is a minimizer of `(Ĉ_L + Ĉ_U)/2` over `[0, ∞)` (p. 16). -/
def IsHatMinimizer (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : Prop :=
  ∀ S' : ℝ≥0, hatObjective P c S ≤ hatObjective P c S'

/-- (4): `C̃(S) = hE[(S-D)⁺] + pE[(D-S)⁺] + (θ/m)E[(S - Σ_{i=1}^m D_i)⁺]`. -/
def tildeC (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : ℝ :=
  backorderCost P.law c.h c.p S + c.θ / c.m * expectedHolding (leadTimeLaw P (c.m - 1)) S

/-- `S̃` is a minimizer of `C̃` over `[0, ∞)` (p. 10). -/
def IsTildeMinimizer (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : Prop :=
  ∀ S' : ℝ≥0, tildeC P c S ≤ tildeC P c S'

end PerishBaseStock.Lifo


