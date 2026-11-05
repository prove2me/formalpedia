-- Prove2me | Definitions.Def_MosonyiPetz_IsCentralDecomposition
-- name    : MosonyiPetz_IsCentralDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:10.825546+00:00
-- url     : https://prove2.me/theorems/046e69c7-2700-47d2-961b-1f3f6d705fe8
-- title:
--   The family $z_1,\dots,z_r$ of all minimal central projections
-- statement:
--   A finite family $z_1,\dots,z_r$ of matrices is the **central decomposition** of a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal K)$ if
--
--   1. every $z_p$ is a minimal central projection of $\mathcal A$;
--   2. the $z_p$ are pairwise orthogonal: $z_pz_q=0$ for $p\ne q$;
--   3. $\sum_{p=1}^r z_p=I$.
--
--   Distinct minimal central projections are orthogonal, so such a family lists every minimal central projection of $\mathcal A$ exactly once, and $\mathcal A\cong\bigoplus_{p=1}^rM_{n_p}$. This is the meaning of "$z_1,\dots,z_r$ the minimal central projections" on p.9 and in Theorem 1.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, p.9; Theorem 1, p.10

import Mathlib
import Definitions.Def_MosonyiPetz_IsMinimalCentralProjection

open scoped Matrix

namespace MosonyiPetz

/-- **The family of all minimal central projections of a subalgebra.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.9: "Assume that z1, z2, . . . , zr the minimal central projections in DK ... DK is isomorphic
to ⊕_{p=1}^r M_{n_p}"; Theorem 1, p.10: "minimal central projections z1, z2, . . . , zr ∈ DK".

`IsCentralDecomposition A z` (for `z : Fin r → Matrix K K ℂ`) holds when every `z p` is a minimal
central projection of `A`, the `z p` are pairwise orthogonal (`z p * z q = 0` for `p ≠ q`), and
`Σ_p z p = 1`.

**Formalization Note.** Since distinct minimal central projections are orthogonal and the family
sums to the unit, a family with this property lists every minimal central projection of `A`
exactly once: it is "the" minimal central projections, not an arbitrary subfamily. -/
def IsCentralDecomposition {K : Type*} [Fintype K] [DecidableEq K] (A : StarSubalgebra ℂ (Matrix K K ℂ))
    {r : ℕ} (z : Fin r → Matrix K K ℂ) : Prop :=
  (∀ p, IsMinimalCentralProjection A (z p)) ∧ (∀ p q, p ≠ q → z p * z q = 0) ∧ ∑ p, z p = 1

end MosonyiPetz


