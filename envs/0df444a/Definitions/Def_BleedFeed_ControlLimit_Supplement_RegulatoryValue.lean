-- Prove2me | Definitions.Def_BleedFeed_ControlLimit_Supplement_RegulatoryValue
-- name    : BleedFeed_ControlLimit_Supplement_RegulatoryValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:07:43.910708+00:00
-- url     : https://prove2.me/theorems/5fce5b9d-4cc5-41d8-9707-429f6887f33f
-- title:
--   §4.3, p. 18 — regulatory-limit value family, increments, and the candidate limit in Remark 3
-- statement:
--   Fix the biological data, cultivation horizon $I$ and growth-rate distribution $G$ of the published model. Write $P_N$ for the same parameters with only the regulatory limit replaced by $N\in\mathbb N$. Define
--   $$F_P(N)=\int v_{P_N}(0,\mu,0)\,dG(\mu),\qquad \Delta_P(N)=F_P(N+1)-F_P(N).$$
--   The candidate limit from Remark 3 is $L_P=\int\sum_{j<\tilde\imath_\mu}r_{j\mu}\,dG(\mu)$. Defining it does not assert that it is the limit; the companion counterexample distinguishes the two. All values use the immutable published Bellman recursion, including its mandatory first period after a reset. These functions support comparisons over every natural regulatory limit without changing any other parameter.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f3359aaff884b6a5f15444a500c2372a3139920a35d2b3e56cfa43906), p. 18 (PDF 18), §4.3, Theorem 4 and Remark 3; pp. 36–38, proof of Theorem 4

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit.Supplement

/-- Change only the regulatory limit; all biological data and the rate law remain fixed. -/
def withLimit (P : Params) (N : ℕ) : Params := { P with N := N }

/-- The performance metric on p. 18, with the initial rate distributed according to G. -/
noncomputable def F (P : Params) (N : ℕ) : ℝ :=
  ∫ μ, v (withLimit P N) 0 μ 0 ∂P.G

/-- Marginal increment when one additional bleed–feed is permitted. -/
noncomputable def increment (P : Params) (N : ℕ) : ℝ := F P (N + 1) - F P N

/-- The candidate limit specified by Remark 3; this is not asserted to be a valid limit. -/
noncomputable def criticalReward (P : Params) : ℝ :=
  ∫ μ, ∑ j ∈ Finset.range (critAge P μ), r P j μ ∂P.G

end BleedFeed.ControlLimit.Supplement


