-- Prove2me | Definitions.Def_MosonyiPetz_multiplicity
-- name    : MosonyiPetz_multiplicity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:07.148198+00:00
-- url     : https://prove2.me/theorems/4f7e04c9-1ece-498c-b9fd-0c4dca844981
-- title:
--   Multiplicity $m$ of a central block
-- statement:
--   For a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal H)$ and a minimal central projection $z$, the block $z\mathcal A$ acts on the range of $z$ as $M_d\otimes I_m$; the number $m$ is its **multiplicity**. Intrinsically, $m$ is the rank of any minimal projection $q$ of $\mathcal A$ with $q\le z$ (p.6: "the rank of any minimal projection in $P_m\mathcal A$ is $m$"):
--
--   $$\operatorname{mult}(z)=\min\{\operatorname{rank}q:\ q \text{ a minimal projection of }\mathcal A,\ zq=q\}.$$
--
--   **Formalization Note** For a minimal central projection the set of these ranks is a single number, so the minimum involves no choice. The value on a projection with no minimal projection below it ($z=0$) is the junk value $0$; the definition is used only on minimal central projections.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, eq. (9), p.5, and proof of Proposition 2, p.6

import Mathlib
import Definitions.Def_MosonyiPetz_IsMinimalProjection

open scoped Matrix

namespace MosonyiPetz

/-- **The multiplicity of a central block.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.5, (9): "m denotes the multiplicity and d the dimension of the block A(m, d, i)"; p.6: "the
rank of any minimal projection in PmA is m".

For a projection `z`, `multiplicity A z` is the rank of a minimal projection `q` of `A` lying
below `z` (`z * q = q`). For a minimal central projection `z` all such `q` have the same rank, the
multiplicity `m` of the block `zA ≅ M_d`, which acts on `ℂ^d ⊗ ℂ^m` as `a ↦ a ⊗ I_m`.

**Formalization Note.** Defined as the least such rank (`sInf` on `ℕ`); for a minimal central
projection the set of ranks is a nonempty singleton, so no choice is involved. On a `z` with no
minimal projection below it (`z = 0`) the value is the junk `0`; the definition is only used on
minimal central projections. -/
noncomputable def multiplicity {H : Type*} [Fintype H] [DecidableEq H] (A : StarSubalgebra ℂ (Matrix H H ℂ))
    (z : Matrix H H ℂ) : ℕ :=
  sInf {n | ∃ q, IsMinimalProjection A q ∧ z * q = q ∧ q.rank = n}

end MosonyiPetz


