-- Prove2me | Definitions.Def_MosonyiPetz_IsMinimalCentralProjection
-- name    : MosonyiPetz_IsMinimalCentralProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:14.113816+00:00
-- url     : https://prove2.me/theorems/cb67a842-e2a6-4b12-b163-92a7c3a5e093
-- title:
--   Minimal central projection of a $*$-subalgebra
-- statement:
--   A central projection $z$ of a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal K)$ is **minimal** if $z\neq0$ and every central projection $w$ of $\mathcal A$ with $w\le z$ (that is, $wz=w$) equals $0$ or $z$.
--
--   For a minimal central projection $z$, $z\mathcal A$ is a full matrix algebra $M_{n}$ (p.9), a block of the decomposition (9).
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, p.9; Theorem 1, p.10

import Mathlib
import Definitions.Def_MosonyiPetz_IsCentralProjection

open scoped Matrix

namespace MosonyiPetz

/-- **A minimal central projection of a subalgebra.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.9: "Assume that z1, z2, . . . , zr the minimal central projections in DK. Then zpDK is
isomorphic to a full matrix algebra"; Theorem 1, p.10.

`IsMinimalCentralProjection A z` holds when `z` is a nonzero central projection of `A` and every
central projection `w` of `A` below `z` (`w * z = w`) is `0` or `z`. -/
def IsMinimalCentralProjection {K : Type*} [Fintype K] [DecidableEq K] (A : StarSubalgebra ℂ (Matrix K K ℂ))
    (z : Matrix K K ℂ) : Prop :=
  IsCentralProjection A z ∧ z ≠ 0 ∧
    ∀ w, IsCentralProjection A w → w * z = w → w = 0 ∨ w = z

end MosonyiPetz


