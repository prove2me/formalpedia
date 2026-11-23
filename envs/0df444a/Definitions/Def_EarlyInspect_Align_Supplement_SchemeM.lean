-- Prove2me | Definitions.Def_EarlyInspect_Align_Supplement_SchemeM
-- name    : EarlyInspect_Align_Supplement_SchemeM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:37:37.755749+00:00
-- url     : https://prove2.me/theorems/5d63abc8-852d-493c-a034-9c3e40a0cbe1
-- title:
--   §3.1, eq. (3) and Theorem 1, p. 60 — the score under scheme $[M]$ for a demand law $P$, and $r=F/f$
-- statement:
--   These are the two objects of Theorem 1 of Alp and Şen, for the **end-of-period inspection scheme** $[M]$ and an arbitrary demand law.
--
--   Let $P$ be the law on $\mathbb R$ of the period demand $D$. An agent who raises the stock to the order-up-to level $S$ is charged $\hat c_o$ per unit of leftover stock, and a lump sum $M$ if the stock has run out at the end of the period. The expected score, which the agent minimizes, is eq. (3) of the paper:
--
--   $$
--   \mathrm{ETPM}_{[M]}(S)=\hat c_o\,\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{D\ge S\}.
--   $$
--
--   For a density $f$ of $P$, with distribution function $F(x)=\mathbb P\{D\le x\}$, the **reciprocal of the reversed hazard rate** is
--
--   $$
--   r(x)=\frac{F(x)}{f(x)}.
--   $$
--
--   Theorem 1 expresses the agent's optimal order-up-to level through the inverse of $r$. The early-inspection score of the paper's eq. (4) is a different function, defined in `EarlyInspect.Align.Model` for normal demand and $\hat c_o=1$.
--
--   **Formalization Note** The penalty uses the closed half-line $\{D\ge S\}$, as printed. The definitions are total: the expectation is $0$ by convention when $(S-D)^+$ is not integrable, the probability is real-valued, and $r(x)=0$ where $f(x)=0$. Theorem 1 assumes a probability law with integrable negative part, and evaluates $r$ only where $f>0$, so none of these default values is used there.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), p. 60 (PDF 7), §3.1 eq. (3) and §4.1.1, Theorem 1 (definition of r)

import Mathlib

namespace EarlyInspect.Align.Supplement

open MeasureTheory ProbabilityTheory

/-- The agent's expected score under scheme `[M]`, eq. (3), p. 60, for a demand law `P`:
`ĉ_o · E[(S − D)^+] + M · P{D ≥ S}`, with `chat` standing for `ĉ_o`. -/
noncomputable def agentCostM (P : Measure ℝ) (chat M S : ℝ) : ℝ :=
  chat * (∫ x, max (S - x) 0 ∂P) + M * P.real (Set.Ici S)

/-- `r(x) = F(x)/f(x)`, the reciprocal of the reversed hazard rate of Theorem 1, p. 60,
for the demand law `P` with distribution function `F = cdf P` and density `f`. -/
noncomputable def revHazardRecip (P : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  cdf P x / f x

end EarlyInspect.Align.Supplement


