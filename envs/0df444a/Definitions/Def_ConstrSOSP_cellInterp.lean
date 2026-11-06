-- Prove2me | Definitions.Def_ConstrSOSP_cellInterp
-- name    : ConstrSOSP_cellInterp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:41.365584+00:00
-- url     : https://prove2.me/theorems/147a2564-8439-4739-82df-b0e77341253e
-- title:
--   Piecewise biquintic interpolation over unit cells
-- statement:
--   Given grid values and gradients on the integer points and a range of cells $\mathrm{Box}(a,b)=[a,a+1]\times[b,b+1]$, $lo\le a,b\le hi-1$, the interpolated function is, on each cell, the Hermite polynomial $f_{-1/2}$ of (17) with that cell's corner data, evaluated at local coordinates. The corner Hessian is $-\tfrac12I$ and the mixed corner data are zero (p.23).
--
--   **Formalization Note** The cell of $z$ is $\lfloor z_i\rfloor$ clamped to the range; adjacent polynomials agree on common edges. Outside $[lo,hi]^2$ the function continues the outermost cells' polynomials; only its restriction to $[lo,hi]^2$ is the paper's object.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.2, pp.23–24; (13), p.22

import Mathlib
import Definitions.Def_ConstrSOSP_fsigma

namespace ConstrSOSP

/-- **Piecewise biquintic interpolation of grid data over the cells `Box(a, b)`**
(arXiv:2604.02285, 2 Nov 2026, §5.2, pp.23–24: "We apply biquintic interpolation in every small
box of G to define f everywhere in [0, N]^2", with `Box(a, b) = [a, a + 1] × [b, b + 1]` (13),
p.22, and corner Hessian `−½ I`, p.23).

For grid data `val (a, b)` and `grad (a, b)` on the integer points and a range of cells
`lo ≤ a, b ≤ hi − 1`, the value at `z` is the Hermite polynomial `f_{−1/2}` of (17) (`fsigma`) of
the cell `Box(a, b)` that contains `z`, with the corner data of that cell, at the local
coordinates `(z₁ − a, z₂ − b)`.

**Formalization Note** The cell index is `⌊zᵢ⌋` clamped to `[lo, hi − 1]`; on a common edge the
two adjacent polynomials agree (p.24), so the choice there is immaterial. Outside `[lo, hi]²` the
function continues the polynomials of the outermost cells; only its restriction to `[lo, hi]²` is
the paper's object. -/
noncomputable def cellInterp (val : ℤ → ℤ → ℝ) (grad : ℤ → ℤ → Fin 2 → ℝ) (lo hi : ℤ)
    (z : Fin 2 → ℝ) : ℝ :=
  let a : ℤ := max lo (min (hi - 1) ⌊z 0⌋)
  let b : ℤ := max lo (min (hi - 1) ⌊z 1⌋)
  fsigma (-1 / 2) (fun i j => val (a + (i : ℕ)) (b + (j : ℕ)))
    (fun i j => grad (a + (i : ℕ)) (b + (j : ℕ)) 0) (fun i j => grad (a + (i : ℕ)) (b + (j : ℕ)) 1)
    (z 0 - a) (z 1 - b)

end ConstrSOSP


