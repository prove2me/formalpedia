-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsSPSolution
-- name    : RBMSensitivity_Data_IsSPSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:47.543997+00:00
-- url     : https://prove2.me/theorems/26b86d2d-fc62-4ee0-b843-1917461c5589
-- title:
--   Definition 4.1: solution of the Skorokhod problem
-- statement:
--   Given $f\in\mathbb C_G(\mathbb R^J)$, a pair $(h,g)\in\mathbb C(\mathbb R^J)\times\mathbb C(\mathbb R^J)$ is a **solution to the SP** $\{(d_i(\alpha),n_i),i\in\mathcal I\}$ for $f$ if $h(0)=f(0)$, and if for all $t\ge 0$:
--
--   1. $h(t)=f(t)+g(t)$;
--   2. $h(t)\in G$;
--   3. for every $s\in[0,t)$, $g(t)-g(s)\in\mathrm{cone}\big[\bigcup_{u\in(s,t]}d(\alpha,h(u))\big]$.
--
--   The RBM is the Skorokhod problem applied pathwise to $x+b(\alpha)t+\sigma(\alpha)W(t)$, so this is the deterministic core of the mission.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 4.1, p.11

import Mathlib
import Definitions.Def_RBMSensitivity_Data_coneAlong
import Definitions.Def_RBMSensitivity_SimpleCone_G
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Definition 4.1: arXiv:1907.00472v2, p.11. Given `f ∈ C_G(ℝ^J)`, `(h, g) ∈ C(ℝ^J) × C(ℝ^J)` solves the
SP `{(d_i(α), n_i), i ∈ I}` for `f` if `h(0) = f(0)` and for all `t ≥ 0`: `h(t) = f(t) + g(t)`;
`h(t) ∈ G`; and for every `s ∈ [0, t)`, `g(t) - g(s) ∈ cone[⋃_{u ∈ (s,t]} d(α, h(u))]`. -/
structure Data.IsSPSolution {J : ℕ} (D : Data J) (α : ℝ) (f h g : ℝ≥0 → E J) : Prop where
  f_continuous : Continuous f
  f_zero : f 0 ∈ D.G
  h_continuous : Continuous h
  g_continuous : Continuous g
  h_zero : h 0 = f 0
  eq : ∀ t, h t = f t + g t
  mem : ∀ t, h t ∈ D.G
  increment : ∀ s t, s < t → g t - g s ∈ D.coneAlong α h s t

end RBMSensitivity


