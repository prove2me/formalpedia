-- Prove2me | Definitions.Def_FastRatesSVM_Rates_Extension
-- name    : FastRatesSVM_Rates_Extension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:31.899563+00:00
-- url     : https://prove2.me/theorems/3494d172-c218-4609-bf20-cb2032435ed9
-- title:
--   Equation (23) — radial extension of the regression function
-- statement:
--   Let $X$ be the unit ball and $\widetilde X=3X$. The regression function is extended radially by
--   $$
--   \widetilde\eta(x)=
--   \begin{cases}\eta(x),&\|x\|\le1,\\
--   \eta(x/\|x\|),&\|x\|>1.
--   \end{cases}
--   $$
--   The enlarged positive and negative classes are the points of $\widetilde X$ where $\widetilde\eta$ is respectively above or below $1/2$.
--
--   This extension appears in Lemma 4.1 and the paper's approximation argument.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 15, (23), Lemma 4.1

import Definitions.Def_FastRatesSVM_Rates_Noise

namespace FastRatesSVM.Rates

def extendedX (d : ℕ) : Set (E d) := Metric.closedBall 0 3

/-- Equation (23): radial extension of the regression function to `3X`. -/
noncomputable def extendedEta {d : ℕ} (D : BinaryDistribution d) (x : E d) : ℝ :=
  if ‖x‖ ≤ 1 then D.η x else D.η ((‖x‖⁻¹) • x)

def extendedPlus {d : ℕ} (D : BinaryDistribution d) : Set (E d) :=
  {x | x ∈ extendedX d ∧ 1 / 2 < extendedEta D x}

def extendedMinus {d : ℕ} (D : BinaryDistribution d) : Set (E d) :=
  {x | x ∈ extendedX d ∧ extendedEta D x < 1 / 2}

end FastRatesSVM.Rates


