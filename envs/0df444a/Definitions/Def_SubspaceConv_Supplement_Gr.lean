-- Prove2me | Definitions.Def_SubspaceConv_Supplement_Gr
-- name    : SubspaceConv_Supplement_Gr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:44:47.280566+00:00
-- url     : https://prove2.me/theorems/d5b0801f-0734-42e4-8b7f-070255bef557
-- title:
--   Grassmannian tables $\mathrm{Gr}_q(n,j)$
-- statement:
--   For a finite field $\mathbb F_q$ and integers $n, j \ge 0$, $\mathrm{Gr}_q(n,j)$ is the set of $j$-dimensional linear subspaces of $\mathbb F_q^n$. It is finite (and empty when $j > n$); its cardinality $|\mathrm{Gr}_q(n,j)|$ is the Gaussian binomial coefficient.
--
--   These sets index the input and output tables of the incidence transform (Theorems 2 and 7) and the vertex set $V = \mathrm{Gr}_q(n,k)$ of the Grassmann graph (Theorem 3).
--
--   **Formalization Note** $\mathbb F_q^n$ is `Fin n → F`, dimension is `Module.finrank`, and table sizes are `Fintype.card` of the subtype, with a noncomputable `Fintype` instance. It complements the published `SubspaceConv.SubLE`, the subspaces of dimension at most $k$.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §1.1, p.2 (PDF p.3)

import Mathlib

set_option autoImplicit false

namespace SubspaceConv.Supplement

/-- `Gr_q(n, j)`, the subspaces of `F^n` of dimension exactly `j` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, p.2 (PDF p.3)).

**Formalization Note** `F^n` is `Fin n → F` and dimension is `Module.finrank`, as in the published
`SubspaceConv.SubLE` (dimension at most `k`). For `j > n` the type is empty. For a finite field the
type is finite, and a `Fintype` instance is provided noncomputably; table sizes such as
`|Gr_q(n, a)|` are `Fintype.card (Gr F n a)`. -/
abbrev Gr (F : Type*) [Field F] (n j : ℕ) : Type _ :=
  {W : Submodule F (Fin n → F) // Module.finrank F W = j}

noncomputable instance (F : Type*) [Field F] [Finite F] (n j : ℕ) : Fintype (Gr F n j) :=
  Fintype.ofFinite _

end SubspaceConv.Supplement


