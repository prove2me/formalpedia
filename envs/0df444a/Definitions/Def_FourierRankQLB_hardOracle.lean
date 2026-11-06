-- Prove2me | Definitions.Def_FourierRankQLB_hardOracle
-- name    : FourierRankQLB_hardOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:46.627192+00:00
-- url     : https://prove2.me/theorems/c8b4517d-417c-44d2-9f3b-a8b5605a6745
-- title:
--   Exact coherent membership for $K_{s,Q}$
-- statement:
--   Let $(Y,\nu)$ be a measure space with a measurable labelling $\iota:Y\to\mathbb R^n$ fixed independently of $Q$. The exact membership oracle of $K_{s,Q}$ acts as
--   $$
--   U_{K_{s,Q}}|y\rangle|b\rangle=|y\rangle|b\oplus\mathbf 1[\iota(y)\in K_{s,Q}]\rangle .
--   $$
--   Boundary points count as members.
--
--   This is the only access an optimizer has to the hidden matrix $Q$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 2.2, Eq. (6), p.14 and Theorem 5.1, p.31

import Mathlib
import Definitions.Def_FourierRankQLB_flipOn
import Definitions.Def_FourierRankQLB_hardBody

open MeasureTheory

namespace FourierRankQLB

/-- The exact coherent membership oracle of the hard ellipsoid `K_{s,Q}` on the register
`L²(Y, ν) ⊗ ℂ² ⊗ W`, whose labels `y` represent the points `ι y ∈ ℝⁿ`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 2.2, Eq. (6), p. 14 and Theorem 5.1, p. 31.

**Formalization Note.** A finite grid `G` of Definition 2.1 is `Y = G`, counting measure, `ι` the
inclusion; the continuous register is `Y = ℝⁿ`, Lebesgue measure, `ι = id`. The label data
`(Y, ν, ι)` does not depend on `Q`. -/
noncomputable def hardOracle {n : ℕ} {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Y → Ambient n) (hι : Measurable ι) (s : ℝ)
    (Q : Od (dn n)) : QReg ν W ≃ₗᵢ[ℂ] QReg ν W :=
  flipOn ν W (ι ⁻¹' hardBody s Q) (hι (measurableSet_hardBody s Q))

end FourierRankQLB


