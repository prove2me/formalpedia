-- Prove2me | Definitions.Def_BlockBochner_Supplement_tiltedDensity
-- name    : BlockBochner_Supplement_tiltedDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:28:57.245396+00:00
-- url     : https://prove2.me/theorems/7e25d411-4a0b-4355-b748-7a293fd66ecb
-- title:
--   Density of the tilted Haar measure $\nu_h$
-- statement:
--   For $h\in\mathbb R^N$ the tilted Haar measure on $S^{N-1}$ is
--   $$
--   \nu_h(du)=Z_h^{-1}e^{h\cdot u}\,d\omega(u),\qquad Z_h=\int_{S^{N-1}}e^{h\cdot u}\,d\omega(u).
--   $$
--   This definition is its density $u\mapsto e^{h\cdot u}/Z_h$ with respect to $\omega$.
--
--   It is the conditional law of one spin of the $O(N)$ model given all others (with $h$ replaced by the effective field $h_x+\sum_{y\ne x}J_{xy}\sigma_y$), and so the resampling law of the Glauber dynamics.
--
--   **Formalization Note** Valued in $\mathbb R_{\ge0}$. $Z_h$ is a lower Lebesgue integral converted to a real number; for $N\ge1$ it lies in $[e^{-\|h\|},e^{\|h\|}]$, so the conversion never truncates.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 4.2, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_haarSphere

open MeasureTheory

namespace BlockBochner.Supplement

/-- **Density of the tilted Haar measure `ν_h`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 4.2, p.28: "the
tilted Haar measure `ν_h(du) = Z_h^{−1} e^{h·u} dω(u)` on `S^{N−1}`, where
`Z_h = ∫_{S^{N−1}} e^{h·u} dω(u)`". This is the density `dν_h/dω (u) = e^{h·u}/Z_h`.

**Formalization Note** Valued in `ℝ≥0`; `Z_h` is the lower Lebesgue integral of `e^{h·u}` against
`ω = haarSphere N`, which is finite and positive for `N ≥ 1` (the integrand lies in
`[e^{−‖h‖}, e^{‖h‖}]`), so no truncation occurs. -/
noncomputable def tiltedDensity (N : ℕ) (h : EuclideanSpace ℝ (Fin N)) (u : GraphNNSphere.Sph N) : NNReal :=
  Real.toNNReal (Real.exp (inner ℝ h (u : EuclideanSpace ℝ (Fin N)))) /
    (∫⁻ v, ENNReal.ofReal (Real.exp (inner ℝ h (v : EuclideanSpace ℝ (Fin N)))) ∂haarSphere N).toNNReal

end BlockBochner.Supplement


