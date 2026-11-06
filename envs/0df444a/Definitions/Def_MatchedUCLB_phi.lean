-- Prove2me | Definitions.Def_MatchedUCLB_phi
-- name    : MatchedUCLB_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:27.970873+00:00
-- url     : https://prove2.me/theorems/509131cb-93dd-4830-ba03-40feeba7d5c5
-- title:
--   The smoothing density $\varphi(u)=c_\varphi e^{-1/(1-u^2)}$
-- statement:
--   The **smoothing density** is the even, smooth probability density on $\mathbb R$
--
--   $$
--   \varphi(u)=\begin{cases}c_\varphi\exp\!\Bigl(-\dfrac{1}{1-u^2}\Bigr),&|u|<1,\\[2pt] 0,&|u|\ge1,\end{cases}
--   $$
--
--   where $c_\varphi>0$ is chosen so that $\int_{-1}^1\varphi(u)\,du=1$.
--
--   **Formalization Note** $c_\varphi$ is written as the reciprocal of $\int_{-1}^{1}e^{-1/(1-u^2)}\,du$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition 4.1, p.5

import Mathlib

namespace MatchedUCLB

/-- **The smoothing density `φ`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition 4.1, p.5: "the even smooth probability
density `φ(u) = c_φ exp(−1/(1−u²))` for `|u| < 1` and `φ(u) = 0` otherwise, with `c_φ > 0` chosen so
that `∫_{−1}^1 φ(u) du = 1`".

**Formalization Note.** `c_φ` is written out as the reciprocal of `∫_{−1}^1 exp(−1/(1−u²)) du`
(an interval integral of a continuous, positive function on `(−1, 1)`), so `φ` integrates to `1`. -/
noncomputable def phi (u : ℝ) : ℝ :=
  (∫ w in (-1 : ℝ)..1, if |w| < 1 then Real.exp (-1 / (1 - w ^ 2)) else 0)⁻¹ *
    (if |u| < 1 then Real.exp (-1 / (1 - u ^ 2)) else 0)

end MatchedUCLB


