-- Prove2me | Definitions.Def_MosonyiPetz_IsMinimalProjection
-- name    : MosonyiPetz_IsMinimalProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:19.997207+00:00
-- url     : https://prove2.me/theorems/3f5818cd-bb77-4969-8617-3d7b3379f2a8
-- title:
--   Minimal projection of a $*$-subalgebra
-- statement:
--   A matrix $q$ is a **minimal projection of** a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal H)$ if $q\in\mathcal A$, $q^2=q=q^*$, $q\ne0$, and every projection $w\in\mathcal A$ with $w\le q$ ($wq=w$) equals $0$ or $q$.
--
--   In a block $M_d\otimes I_m$ of $\mathcal A$ the minimal projections are $e\otimes I_m$ with $e$ of rank one, so they have rank $m$ (p.6).
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, proof of Proposition 2, p.6

import Mathlib

open scoped Matrix

namespace MosonyiPetz

/-- **A minimal projection of a subalgebra.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.6 (proof of Proposition 2): "the rank of any minimal projection in PmA is m", "let q ∈ Pm1A be
a minimal projection".

`IsMinimalProjection A q` holds when `q ∈ A` is a nonzero orthogonal projection (`q * q = q`,
`qᴴ = q`) and every orthogonal projection `w ∈ A` below `q` (`w * q = w`) is `0` or `q`. -/
def IsMinimalProjection {H : Type*} [Fintype H] [DecidableEq H] (A : StarSubalgebra ℂ (Matrix H H ℂ))
    (q : Matrix H H ℂ) : Prop :=
  q ∈ A ∧ q * q = q ∧ qᴴ = q ∧ q ≠ 0 ∧
    ∀ w ∈ A, w * w = w → wᴴ = w → w * q = w → w = 0 ∨ w = q

end MosonyiPetz


