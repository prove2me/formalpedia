-- Prove2me | Definitions.Def_SecondBestBT_gridPrior
-- name    : SecondBestBT_gridPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:43.979542+00:00
-- url     : https://prove2.me/theorems/0ff0b19a-1f4c-4e83-a705-e9ffbbc0e048
-- title:
--   Grid prior $\sum_i f(i)\,\delta_{t_i}$
-- statement:
--   Given grid points $t_0,\dots,t_N$ and masses $f(0),\dots,f(N)$, the **grid prior** is the measure
--   $$
--   \sum_{i=0}^{N} f(i)\,\delta_{t_i}
--   $$
--   on $\mathbb R$. With $0=t_0<\dots<t_N=1$ it is a prior supported on the finite grid $D$ of Section 3; with $t_i=i$ it is a prior on the integer grid $Z_W=\{0,\dots,W\}$ of Section 4.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- The prior on `ℝ` with mass `f(i)` at the grid point `t_i`, `i = 0, …, N`:
`∑ᵢ f(i) δ_{t_i}` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 3,
p.6: priors supported on a finite grid `D = {0 = t_0 < ⋯ < t_N = 1}`; with `t_i = i`, the priors
on `Z_W = {0, …, W}` of p.7).

**Formalization Note** Masses are real and enter through `ENNReal.ofReal`; for an `IsGridPMF`
vector this is a probability measure. -/
noncomputable def gridPrior (t : ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) : Measure ℝ :=
  ∑ i ∈ Finset.range (N + 1), ENNReal.ofReal (f i) • Measure.dirac (t i)

end SecondBestBT


