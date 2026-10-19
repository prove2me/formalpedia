-- Prove2me | Definitions.Def_UnknownProphet_NoSamples_FinDist
-- name    : UnknownProphet_NoSamples_FinDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:37.357305+00:00
-- url     : https://prove2.me/theorems/1b7d9fee-bad9-4860-bb74-e9be69e9035a
-- title:
--   §2, p. 5 — finitely supported nonnegative distribution and independent draws
-- statement:
--   A **finite distribution** $F$ on nonnegative real values consists of a finite support $S\subseteq[0,\infty)$ and nonnegative masses $w(v)$ on $S$ with $\sum_{v\in S}w(v)=1$. For independent draws $x_1,\ldots,x_m$ from $F$, their joint mass is
--
--   $$
--   w_F(x_1,\ldots,x_m)=\prod_{j=1}^{m}w(x_j).
--   $$
--
--   This finite law makes the expectations in the stopping model ordinary finite sums.
--
--   **Formalization Note** Weights outside $S$ are irrelevant. The paper allows arbitrary distributions in its general model; this mission uses finite laws because the upper-bound construction itself has finite support.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 5, §2; p. 7, proof of Theorem 2

import Mathlib

namespace UnknownProphet.NoSamples

/-- A finitely supported probability distribution on the nonnegative reals.
Only the weights on `supp` matter. -/
structure FinDist where
  supp : Finset ℝ
  w : ℝ → ℝ
  supp_nonneg : ∀ v ∈ supp, 0 ≤ v
  w_nonneg : ∀ v ∈ supp, 0 ≤ w v
  w_sum : ∑ v ∈ supp, w v = 1

/-- Product weight for independent draws from a finitely supported distribution. -/
noncomputable def iidWeight (F : FinDist) {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∏ j, F.w (x j)

end UnknownProphet.NoSamples


