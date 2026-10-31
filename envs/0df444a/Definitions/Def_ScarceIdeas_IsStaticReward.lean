-- Prove2me | Definitions.Def_ScarceIdeas_IsStaticReward
-- name    : ScarceIdeas_IsStaticReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:47.645926+00:00
-- url     : https://prove2.me/theorems/cd3d0e47-8ead-4b99-9fd9-aa7d98fe211d
-- title:
--   Static reward at a known arrival rate, equation (56)
-- statement:
--   For an arrival rate $\lambda\ge0$, a reward $q$ is the **static reward** when it solves
--
--   $$\frac vr-q=\frac{\lambda}{r}\int_{\underline c}^{q}F(c)\,dc ,$$
--
--   the optimality condition (8) of the benchmark with a known arrival rate. At $\lambda=m_1(\phi)$ its root is the reward $p_{na}(\phi)$ of a naive planner who ignores learning (Theorem 4).
--
--   **Formalization Note** Defined as the root of (56), as the paper's proof of Theorem 4 does; the identification with the maximiser of the benchmark problem (Theorem 1) is not part of this mission.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Appendix, proof of Theorem 4, (56), p.41; (8), p.14

import Mathlib
import Definitions.Def_ScarceIdeas_costCDF

namespace ScarceIdeas

/-- **Static (naive) reward at a fixed arrival rate, equation (56).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Appendix, proof of Theorem 4, (56), p.41 ("From equation (8), pna(ϕ) is the unique solution
to (56)"), from the benchmark condition (8), p.14.

`IsStaticReward r v cL f lam q` says that `q` solves

$$\frac vr-q=\frac{\lambda}{r}\int_{\underline c}^{q}F(c)\,dc ,$$

the optimality condition of the known-rate benchmark with arrival rate `λ = lam`. Theorem 4
uses it at `λ = m₁(ϕ)`, which defines `p_na(ϕ)`.

**Formalization Note** `p_na` is defined as the root of (56), as the paper's proof does, not as
the maximiser of the benchmark problem (3) (Theorem 1, which identifies the two, is not part of
this mission). For `lam ≥ 0` every root lies in `(c̲, v/r]`. -/
def IsStaticReward (r v cL : ℝ) (f : ℝ → ℝ) (lam q : ℝ) : Prop :=
  v / r - q = lam / r * ∫ c in cL..q, costCDF cL f c

end ScarceIdeas


