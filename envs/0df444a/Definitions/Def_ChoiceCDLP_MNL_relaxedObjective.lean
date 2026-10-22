-- Prove2me | Definitions.Def_ChoiceCDLP_MNL_relaxedObjective
-- name    : ChoiceCDLP_MNL_relaxedObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:42:48.362321+00:00
-- url     : https://prove2.me/theorems/8501cf5b-fede-4809-81cf-550fadba88ef
-- title:
--   Objective of the relaxation (17): h(z) = wᵀz/(eᵀz + v_0) on the box 𝒟 = [0, v_1] × ⋯ × [0, v_s]
-- statement:
--   For scores $w_j$ and a no-purchase weight $v_0$ indexed by a finite consideration set $\iota$, the **relaxed objective** of the paper's problem (17) is the ratio of two affine functions of $z \in \mathbb{R}^\iota$,
--   $$h(z) = \frac{w^\top z}{e^\top z + v_0} = \frac{\sum_{j} w_j z_j}{\sum_j z_j + v_0},$$
--   where $e$ is the all-ones vector. Problem (17) maximizes $h$ over the box $\mathcal{D} = [0, v_1] \times \cdots \times [0, v_s]$, obtained from problem (14) by substituting $z_j = v_j y_j$ and letting each $z_j$ range over the whole interval $[0, v_j]$ instead of $\{0, v_j\}$.
--
--   **Formalization Note.** The box $\mathcal{D}$ is written `Set.Icc 0 v` in the theorems (the componentwise order on `ι → ℝ`). At $z = 0$ with $v_0 = 0$ the quotient is $0/0 = 0$ in Lean, which is the paper's convention $h(0) := 0$ (p. 309).
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 309, Appendix, proof of Proposition 6, problem (17) and the definition of h(z)

import Mathlib

namespace ChoiceCDLP.MNL

/-- The objective of the continuous relaxation (17) of Liu and van Ryzin (2008, Appendix, proof
of Proposition 6, p. 309), `h(z) = wᵀz / (eᵀz + v₀) = (∑_j w_j z_j) / (∑_j z_j + v₀)`, for
`z : ι → ℝ` indexed by the (finite) consideration set `ι`. The feasible region of (17) is the
box `𝒟 = [0, v_1] × ⋯ × [0, v_s]`, which in Lean is `Set.Icc 0 v`.
When `z = 0` and `v₀ = 0` the quotient is `0 / 0 = 0` in Lean, the paper's convention
`h(0) := 0`. -/
noncomputable def relaxedObjective {ι : Type*} [Fintype ι] (w : ι → ℝ) (v₀ : ℝ)
    (z : ι → ℝ) : ℝ :=
  (∑ j, w j * z j) / (∑ j, z j + v₀)

end ChoiceCDLP.MNL


