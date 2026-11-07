-- Prove2me | Definitions.Def_SpectrumLB_prpMatrix
-- name    : SpectrumLB_prpMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:29.990136+00:00
-- url     : https://prove2.me/theorems/e0477470-b880-4835-926f-d010bfe98cfb
-- title:
--   Definition 3.4 — product of random projections $X=W^\dagger W$, $W=\Pi_K\cdots\Pi_1$
-- statement:
--   Let $a=(a_1,\dots,a_K)$ be positive integers and $d$ a multiple of each $a_i$. Given unitaries $U_1,\dots,U_K\in U(d)$, let $\Pi_i=U_iR_{d/a_i}U_i^\dagger$ be the projection of rank $d/a_i$ and
--
--   $$
--   X=W^\dagger W,\qquad W=\Pi_K\Pi_{K-1}\cdots\Pi_2\Pi_1 .
--   $$
--
--   When the $U_i$ are independent and Haar distributed, $X$ has the law $\mathrm{PRP}_d(a)$, the "product of random projections" distribution. It is a random positive semidefinite contraction with $\mathbf E[X]=\nu_a\mathbf 1$, $\nu_a=1/(a_1\cdots a_K)$; normalized and tilted, it produces the two hard ensembles of the lower bound.
--
--   **Formalization Note** $\mathrm{PRP}_d(a)$ is represented through the underlying unitaries: probabilities and expectations about $X$ are taken under the product Haar measure. The rank $d/a_i$ is natural-number division, and every statement using it assumes $a_i\mid d$.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 3.4, Eq. (3.9), p. 14

import Mathlib
import Definitions.Def_SpectrumLB_haarProj

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **The product of random projections `X = W†W`, `W = Π_K ⋯ Π_1`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 3.4, Eq. (3.9), p. 14: "X = W†W, W := Π_K Π_{K−1} ⋯ Π_2 Π_1, where Π_i is a Haar-random
projection of rank d/a_i on C^d, drawn independently for i = 1 … K".

`prpMatrix a U` is `X` as a function of the unitaries `U = (U_1, …, U_K)`, with `Π_i = U_i R_{d/a_i} U_i†`;
under `haarK d K` its law is `PRP_d(a)`.

**Formalization Note.** `PRP_d(a)` is represented through the underlying unitaries (Mathlib has no measurable
structure on `Matrix`): expectations and probabilities about `X ∼ PRP_d(a)` are integrals and measures under
`haarK d K`. The rank `d / a_i` is natural-number division; every statement using it assumes `a_i ∣ d`
(Definition 3.4). The index `i : Fin K` is 0-based. -/
def prpMatrix {d K : ℕ} (a : Fin K → ℕ) (U : Fin K → Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let W := (List.ofFn fun i : Fin K => haarProj (d / a (Fin.rev i)) (U (Fin.rev i))).prod
  Wᴴ * W

end SpectrumLB


