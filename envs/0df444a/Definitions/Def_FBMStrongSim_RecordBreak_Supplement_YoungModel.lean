-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungModel
-- name    : FBMStrongSim_RecordBreak_Supplement_YoungModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:27:32.993824+00:00
-- url     : https://prove2.me/theorems/99ed01c7-76df-47ae-a43b-8a396eb27c7b
-- title:
--   Young solutions without an assumed Hölder bound
-- statement:
--   Let $x:[0,1]\to\mathbb R^h$ be $\alpha$-Hölder, and $f:\mathbb R^d\to\mathbb R^{d\times h}$. A Young solution is a continuous path $y$, starting at $y_0$, with finite $q$-variation for some $q>0$ with $\alpha+1/q>1$, such that
--   $$y(t)-y_0=\int_0^t f(y(s))\,dx(s)\qquad(0\le t\le1).$$
--   The integral is the limit of every left-point Riemann sum as the partition mesh tends to zero, using the published generic `HairerLiFBM.SemiDet.IsYoungIntegral` and `Partition`. Finite variation is expressed by a uniform bound on the sums of $q$th powers of increments over all finite monotone partitions. Under the coefficient bounds, finite compatible variation of $y$ gives that of the integrand $f(y)$. No Hölder estimate for $y$ is built into this definition; Lemma 5.7 establishes it.
--
--   Differences from the source:
--   - encoding: Definitions 5.1–5.2 and the Riemann-sum Young integral → continuity, the initial condition, finite compatible q-variation, and the integral equation using the published generic Partition and IsYoungIntegral; reason: every finite monotone partition is tested; under the bounded derivative assumption composition preserves compatible variation, and no solution Hölder bound is assumed
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, pp. 29–30, Definitions 5.1–5.2

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_CoefficientModel

namespace FBMStrongSim.RecordBreak.Supplement

open HairerLiFBM.SemiDet

/-- Finite q-variation over arbitrary partitions, not a Hölder assumption. -/
def FiniteVariation {E : Type*} [NormedAddCommGroup E] (q : ℝ) (y : ℝ → E) : Prop :=
  ∃ C : ℝ, ∀ p : Partition 0 1,
    (∑ i : Fin p.n, ‖y (p.pt i.succ) - y (p.pt i.castSucc)‖ ^ q) ≤ C

/-- Definitions 5.1–5.2: all left-point Riemann sums, with their full partition domain.
Continuity and finite compatible variation are required; α-Hölder regularity is a conclusion. -/
def YoungSolution {d h : ℕ} (alpha : ℝ) (f : Field d h) (x : ℝ → Vec h)
    (y0 : Vec d) (y : ℝ → Vec d) : Prop :=
  y 0 = y0 ∧ ContinuousOn y (Set.Icc 0 1) ∧
    (∃ q : ℝ, 0 < q ∧ 1 < alpha + 1 / q ∧ FiniteVariation q y) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsYoungIntegral (fun r => f (y r)) x 0 t (y t - y0)


end FBMStrongSim.RecordBreak.Supplement


