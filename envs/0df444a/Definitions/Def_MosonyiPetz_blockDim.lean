-- Prove2me | Definitions.Def_MosonyiPetz_blockDim
-- name    : MosonyiPetz_blockDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:12.452417+00:00
-- url     : https://prove2.me/theorems/31c73ec6-ff7e-45db-a1cc-9533d7c0a109
-- title:
--   Dimension $d$ of a central block
-- statement:
--   For a minimal central projection $z$ of a unital $*$-subalgebra $\mathcal A\subset\mathcal B(\mathcal H)$, the block $z\mathcal A\cong M_d$ acts on the range of $z$, of dimension $md$, as $a\mapsto a\otimes I_m$ with $m$ the multiplicity. Its **dimension** is
--
--   $$d=\frac{\operatorname{rank}z}{\operatorname{mult}(z)}.$$
--
--   **Formalization Note** Natural-number division; for a minimal central projection the rank is an exact multiple of the multiplicity $m\ge1$.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, eq. (9), p.5, and p.6

import Mathlib
import Definitions.Def_MosonyiPetz_multiplicity

open scoped Matrix

namespace MosonyiPetz

/-- **The dimension of a central block.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.5, (9): "d the dimension of the block A(m, d, i)"; p.6: the range of `P_{m,d}` has an
orthonormal basis `{e(m, d, k) : 1 ≤ k ≤ mdK(m, d)}`.

For a minimal central projection `z` of `A`, `blockDim A z = rank z / multiplicity A z`: the block
`zA` is `M_d ⊗ I_m` on the range of `z`, of dimension `m·d`, so this is `d`.

**Formalization Note.** Natural-number division; for a minimal central projection the rank is an
exact multiple `m·d` of the multiplicity `m ≥ 1`, so no truncation occurs there. -/
noncomputable def blockDim {H : Type*} [Fintype H] [DecidableEq H] (A : StarSubalgebra ℂ (Matrix H H ℂ))
    (z : Matrix H H ℂ) : ℕ :=
  z.rank / multiplicity A z

end MosonyiPetz


