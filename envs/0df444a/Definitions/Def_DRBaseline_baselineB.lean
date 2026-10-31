-- Prove2me | Definitions.Def_DRBaseline_baselineB
-- name    : DRBaseline_baselineB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:50.69356+00:00
-- url     : https://prove2.me/theorems/9929817e-fd2d-4561-8e5b-0c697783bf49
-- title:
--   Baseline threshold $B(\Omega,r,c_s)$ of Lemma 2
-- statement:
--   $$B(\Omega,r,c_s)=\begin{cases}B_2(r)=2\Omega-\dfrac{r}{2c_s} & \text{if } r/c_s\le2\Omega,\\[4pt] B_3(r)=\dfrac{2\Omega^2c_s}{r} & \text{otherwise.}\end{cases}$$
--
--   Above this baseline the expected underestimation $X_u(b,r)$ decreases in $b$ (Lemma 2).
--
--   **Formalization Note** $B_3$ is used only when $r/c_s>2\Omega$, so $r>0$ there.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1

import Mathlib

namespace DRBaseline

/-- **Baseline threshold `B(Ω, r, c_s)` of Lemma 2.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Online Appendix, Proof of Proposition 1, and Lemma 1 and 2, p.OA1: "B(·) .= B2(·) if
r/cs ≤ 2Ω and B(·) = B3(·) otherwise", with `B₂(r) = 2Ω − r/(2c_s)` and `B₃(r) = 2Ω²c_s/r`.

**Formalization Note** `B₃` is used only when `r/c_s > 2Ω`, so `r > 0` there and the
division is genuine. -/
noncomputable def baselineB (Ω cs r : ℝ) : ℝ :=
  if r / cs ≤ 2 * Ω then 2 * Ω - r / (2 * cs) else 2 * Ω ^ 2 * cs / r

end DRBaseline


