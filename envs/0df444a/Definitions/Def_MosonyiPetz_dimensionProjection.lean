-- Prove2me | Definitions.Def_MosonyiPetz_dimensionProjection
-- name    : MosonyiPetz_dimensionProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:21.517916+00:00
-- url     : https://prove2.me/theorems/19f67124-91be-44d2-9862-9eec90017edd
-- title:
--   Dimension projection $P_d$
-- statement:
--   For a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal H)$ and $d\in\mathbb N$,
--
--   $$P_d=\sum\{z:\ z\text{ a minimal central projection of }\mathcal A,\ z\mathcal A\cong M_d\},$$
--
--   the projection onto the blocks of dimension $d$ (p.7: $P_d=\oplus_{i}P_{d,i}$). $P_d=0$ when no block has dimension $d$.
--
--   **Formalization Note** A finite sum (`finsum`) over the minimal central projections whose block dimension is $d$; intrinsic, no choice of coordinates.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, pp.6–7

import Mathlib
import Definitions.Def_MosonyiPetz_IsMinimalCentralProjection
import Definitions.Def_MosonyiPetz_blockDim

open scoped Matrix

namespace MosonyiPetz

/-- **The dimension projection P_d.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, pp.6–7: "Pd,i(d′, i′) := δ(d′, d)δ(i′, i)Id, and the projection corresponding to dimension d is
Pd := ⊕_{i=1}^{K(d)} Pd,i."

`dimensionProjection A d` is the sum of all minimal central projections `z` of `A` whose block
`zA ≅ M_d` has dimension `d`. It is `0` when no block has dimension `d`.

**Formalization Note.** A `finsum` over a finite set (as for `multiplicityProjection`), intrinsic
and independent of any choice of the coordinates (9). The paper uses `P_d` in the setting where all
multiplicities are equal (p.6); the definition makes sense for every `A`. -/
noncomputable def dimensionProjection {H : Type*} [Fintype H] [DecidableEq H]
    (A : StarSubalgebra ℂ (Matrix H H ℂ)) (d : ℕ) : Matrix H H ℂ :=
  ∑ᶠ z ∈ {z | IsMinimalCentralProjection A z ∧ blockDim A z = d}, z

end MosonyiPetz


