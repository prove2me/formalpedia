-- Prove2me | Definitions.Def_MosonyiPetz_multiplicityProjection
-- name    : MosonyiPetz_multiplicityProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:08.521237+00:00
-- url     : https://prove2.me/theorems/1bb1a768-bf3f-4661-a90f-276a87bd2ce9
-- title:
--   Multiplicity projection $P_m$
-- statement:
--   For a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal H)$ and $m\in\mathbb N$,
--
--   $$P_m=\sum\{z:\ z\text{ a minimal central projection of }\mathcal A,\ \operatorname{mult}(z)=m\},$$
--
--   the projection onto the blocks of multiplicity $m$ (p.6: $P_m=\oplus_dP_{m,d}$). $P_m=0$ when no block has multiplicity $m$. Proposition 2 says that a unitary normalizing $\mathcal A$ commutes with every $P_m$.
--
--   **Formalization Note** A sum over the finite set of minimal central projections with the given multiplicity (`finsum`). It is intrinsic: no choice of the coordinates (9) is involved.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, pp.5–6

import Mathlib
import Definitions.Def_MosonyiPetz_IsMinimalCentralProjection
import Definitions.Def_MosonyiPetz_multiplicity

open scoped Matrix

namespace MosonyiPetz

/-- **The multiplicity projection P_m.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, pp.5–6: "Let Pm,d be the projection in A corresponding to multiplicity m and dimension d ...
and let Pm := ⊕_d Pm,d be the projection corresponding to the multiplicity m."

`multiplicityProjection A m` is the sum of all minimal central projections `z` of `A` whose block
has multiplicity `m`. It is `0` when no block has multiplicity `m`.

**Formalization Note.** The sum is a `finsum` over the set of such `z`. A finite-dimensional
algebra has finitely many minimal central projections (they are nonzero and pairwise orthogonal),
so the sum is the ordinary finite sum; it is intrinsic and needs no choice of decomposition (9). -/
noncomputable def multiplicityProjection {H : Type*} [Fintype H] [DecidableEq H]
    (A : StarSubalgebra ℂ (Matrix H H ℂ)) (m : ℕ) : Matrix H H ℂ :=
  ∑ᶠ z ∈ {z | IsMinimalCentralProjection A z ∧ multiplicity A z = m}, z

end MosonyiPetz


