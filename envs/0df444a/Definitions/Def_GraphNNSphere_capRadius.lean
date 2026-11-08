-- Prove2me | Definitions.Def_GraphNNSphere_capRadius
-- name    : GraphNNSphere_capRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:41:30.300624+00:00
-- url     : https://prove2.me/theorems/cb954330-96bd-4ddd-ae82-b4fe4ec5982a
-- title:
--   Cap radius of mass $m$
-- statement:
--   For $m\in[0,1]$ and $d\ge 2$, the radius $\theta\in[0,\pi]$ with $F_{d-1}(\theta)=m$. The radii $\theta_1,\rho_\beta,r_\gamma,\vartheta$ of the paper are all of this form, with $m$ equal to $1/n$, $n^\beta/n$, $e^{\gamma d}/n$ and $T/n$.
--
--   **Formalization Note** The solution is encoded as $\inf\{\theta\in[0,\pi]:m\le F_{d-1}(\theta)\}$. For $d\ge2$ the function $F_{d-1}$ is continuous and strictly increasing on $[0,\pi]$ with $F(0)=0$ and $F(\pi)=1$, so the infimum is the unique solution. For $m>1$ the set is empty and the value is the junk value $0$; the theorems that use a mass that could exceed $1$ have hypotheses that exclude this value.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3; §2.2, p.15; §3.3, p.23

import Mathlib
import Definitions.Def_GraphNNSphere_capMass

namespace GraphNNSphere

/-- The cap radius of mass `m`: the solution `θ ∈ [0, π]` of `F_{d-1}(θ) = m`, for `m ∈ [0, 1]`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission
(manuscript sha256 93565bc5…), pp.3, 15, 23).

**Formalization Note** The solution is encoded as the infimum of `{θ ∈ [0, π] | m ≤ F(θ)}`. For
`d ≥ 2` the function `F` is continuous and strictly increasing on `[0, π]` with `F(0) = 0` and
`F(π) = 1`, so the infimum is the unique solution when `m ∈ [0, 1]`. For `m > 1` the set is empty
and the value is the junk value `0`. -/
noncomputable def capRadius (d : ℕ) (m : ℝ) : ℝ :=
  sInf {θ | θ ∈ Set.Icc 0 Real.pi ∧ m ≤ capMass d θ}

end GraphNNSphere


