-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_GeometricLaw
-- name    : MoneyBurningTrade_IndependentSurplus_Supplement_GeometricLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:21.914197+00:00
-- url     : https://prove2.me/theorems/d655262e-2918-405c-98e9-ef6c5c092375
-- title:
--   Equation (28) — the geometric grid and the correlated law F^n
-- statement:
--   For an integer $n\ge4$ let $R=\sqrt n$ and
--
--   $$q_i=R^{\,i-n}\qquad(i=0,\dots,n),$$
--
--   so $q_i=Rq_{i-1}$ and $q_n=1$. Let $Z=\sum_{r=1}^n 1/q_r$. The joint law $F^n$ puts probability
--
--   $$\pi_i=\frac{1}{Z\,q_i}$$
--
--   on the profile $(v_s,v_b)=(q_{i-1},q_i)$ for each $i\in[n]$ and no mass elsewhere. The probability of each profile is inversely proportional to its buyer's value. This is the witness of Theorem 5.2.
--
--   **Formalization Note** $q_i$ uses an integer exponent. The law is the finite sum of weighted Dirac masses at the exact atoms (not the continuous variant of footnote 12); its normalization is left to theorems.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §5.2, "The distributions", equation (28), printed p. 33 (PDF p. 34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- `R = √n`, §5.2 p.33. -/
noncomputable def geomRatio (n : ℕ) : ℝ := Real.sqrt n

/-- The geometric grid of §5.2 p.33: `q_i = R^(i−n)` (integer exponent), so
`q_i = R·q_{i−1}` and `q_n = 1`. Used for `i ∈ {0,…,n}`. -/
noncomputable def geomGrid (n i : ℕ) : ℝ := geomRatio n ^ ((i : ℤ) - n)

/-- `Z = Σ_{r=1}^n 1/q_r`, equation (28). -/
noncomputable def geomZ (n : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 n, 1 / geomGrid n r

/-- The correlated law `F^n` of (28), §5.2 p.33: probability `π_i = 1/(Z q_i)` on the
profile `(q_{i−1}, q_i)` (seller's value first) for `i ∈ [n]`; no other mass.
These are the exact atoms, not footnote 12's continuous variant. -/
noncomputable def geomLaw (n : ℕ) : Measure (ℝ × ℝ) :=
  ∑ i ∈ Finset.Icc 1 n, ENNReal.ofReal (1 / (geomZ n * geomGrid n i)) •
    Measure.dirac (geomGrid n (i - 1), geomGrid n i)

end MoneyBurningTrade.IndependentSurplus.Supplement


