-- Prove2me | Definitions.Def_LeGallBrownianMap_rescaledTriple
-- name    : LeGallBrownianMap_rescaledTriple
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:53.86975+00:00
-- url     : https://prove2.me/theorems/b398cbd5-4bdb-4e0e-8bc5-0ba27773172c
-- title:
--   The rescaled contour, label and distance processes of eq. (5)
-- statement:
--   For $\theta\in\mathbb T^p_n$ with contour function $C_i=\tfrac12|v_i|$, label function $\Lambda_i$ and distance process $d_n$, the triple of continuous processes
--
--   $$
--   \Big(\lambda_p n^{-1/2} C_{pnt},\ \kappa_p n^{-1/4}\Lambda_{pnt},\ \kappa_p n^{-1/4} d_n(pns,pnt)\Big)_{0\le s,t\le1},
--   $$
--
--   with $C$ and $\Lambda$ linearly interpolated. This is the left-hand side of the convergence (5) in Theorem 2.3.
--
--   **Formalization Note** Each component is an element of the space of functions with the topology of uniform convergence (`UniformFun`).
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.9; §2.5, pp.15–16, eq. (5)

import Mathlib
import Definitions.Def_LeGallBrownianMap_labelSeq
import Definitions.Def_LeGallBrownianMap_linInterp
import Definitions.Def_LeGallBrownianMap_distInterp
import Definitions.Def_LeGallBrownianMap_lambdaP
import Definitions.Def_LeGallBrownianMap_kappaP

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.9
("The contour function of τ° is the discrete sequence C^τ°_0, ..., C^τ°_{pn} defined by
C^τ°_i = ½|v_i|"), §2.5, pp.15–16, and the left-hand side of eq. (5), p.16:
"(λ_p n^{−1/2} C^n_{pnt}, κ_p n^{−1/4} Λ^n_{pnt}, κ_p n^{−1/4} d_n(pns, pnt))_{0≤s≤1, 0≤t≤1}".

`rescaledTriple p n θ` is this triple of processes for the labeled p-tree `θ ∈ T^p_n`: the
rescaled linearly interpolated contour function, label function, and interpolated distance
process, as functions on `[0,1]` and `[0,1]²`.

**Formalization Note.** The processes are elements of the spaces `UniformFun` of functions with
the topology of uniform convergence; all three are continuous, so convergence in distribution in
this space is convergence in distribution of continuous processes for the sup norm. Real
powers are `Real.rpow`. -/
noncomputable def rescaledTriple (p n : ℕ) (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) :
    UniformFun unitInterval ℝ × UniformFun unitInterval ℝ ×
      UniformFun (unitInterval × unitInterval) ℝ :=
  (UniformFun.ofFun fun t => lambdaP p * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      linInterp (fun i => ((contourSeq θ.1 i).length : ℝ) / 2) ((p * n : ℝ) * t),
    UniformFun.ofFun fun t => kappaP p * (n : ℝ) ^ (-(1 / 4 : ℝ)) *
      linInterp (fun i => (labelSeq θ i : ℝ)) ((p * n : ℝ) * t),
    UniformFun.ofFun fun x => kappaP p * (n : ℝ) ^ (-(1 / 4 : ℝ)) *
      distInterp θ ((p * n : ℝ) * x.1) ((p * n : ℝ) * x.2))

end LeGallBrownianMap


