-- Prove2me | Definitions.Def_CubeSampling_cubeDeriv
-- name    : CubeSampling_cubeDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:57.290072+00:00
-- url     : https://prove2.me/theorems/0f5f6df0-e032-470b-b3ec-67805134fd74
-- title:
--   Partial derivative $\partial_i f$ on the cube
-- statement:
--   For $f$ on $\{-1,1\}^d$ and $i \in [d]$,
--   $$
--   \partial_i f(x) = \frac{f(x^{i\to 1}) - f(x^{i\to -1})}{2},
--   $$
--   where $x^{i\to\pm1}$ is $x$ with its $i$-th coordinate set to $\pm 1$. For a multilinear polynomial $f = \sum_S c_S\chi_S$ this is $\sum_{S \ni i} c_S\,\chi_{S\setminus\{i\}}$, the usual partial derivative.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 5, p.19

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- The partial derivative `∂_i f(x) = (f(x^{i→1}) − f(x^{i→−1}))/2` on the cube (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §5, p.19).

**Formalization Note** For a multilinear `f = ∑_S c_S χ_S` this is `∑_{S ∋ i} c_S χ_{S∖{i}}`, the
partial derivative of the multilinear polynomial. -/
noncomputable def cubeDeriv {d : ℕ} (i : Fin d) (f : Cube d → ℝ) (x : Cube d) : ℝ :=
  (f (Function.update x i true) - f (Function.update x i false)) / 2

end CubeSampling


