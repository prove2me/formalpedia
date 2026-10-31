-- Prove2me | Definitions.Def_DeltaSLearning_cycleGrad
-- name    : DeltaSLearning_cycleGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:47.034099+00:00
-- url     : https://prove2.me/theorems/6d7d22ea-4514-4810-89c3-ae6b1d002b9f
-- title:
--   Stochastic gradient $\tilde\nabla$ of a cycle (11)
-- statement:
--   For a demand path, a gap $\delta$ and a target $S$, with $L=L(\delta)$ and ending inventory $x_{L+1}=(S-d_0-\dots-d_{L-1})^+$,
--   $$\tilde\nabla := \begin{cases} hL, & x_{L+1}>0,\\ h(L-1)-p+c, & x_{L+1}=0.\end{cases}$$
--   This is the pathwise derivative of the cycle pseudo cost $G(\delta,S)$ in $S$ (49), and Theorem 2(b) states that it is an unbiased gradient of $\mathbb E[G(\delta,S)]$.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (11), p.12; eq. (49), p.37

import Mathlib
import Definitions.Def_DeltaSLearning_Params
import Definitions.Def_DeltaSLearning_cycleLength

namespace DeltaSLearning

/-- The stochastic gradient (11) of one cycle of a `(δ, S)` policy started at level `S`:
`∇̃ = h L` if the ending inventory `x_{L+1} = (S - (d 0 + ⋯ + d (L-1)))⁺` is positive, and
`∇̃ = h (L - 1) - p + c` if `x_{L+1} = 0`, where `L = L(δ)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (11), p.12, and eq. (49), p.37.

**Formalization Note** `L - 1` is computed in `ℝ`, not `ℕ`. -/
noncomputable def cycleGrad (cp : Params) (δ S : ℝ) (d : ℕ → ℝ) : ℝ :=
  if 0 < max (S - ∑ i ∈ Finset.range (cycleLength δ d), d i) 0 then
    cp.h * (cycleLength δ d : ℝ)
  else
    cp.h * ((cycleLength δ d : ℝ) - 1) - cp.p + cp.c

end DeltaSLearning


