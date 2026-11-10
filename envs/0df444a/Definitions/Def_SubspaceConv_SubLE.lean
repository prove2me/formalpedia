-- Prove2me | Definitions.Def_SubspaceConv_SubLE
-- name    : SubspaceConv_SubLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:19.543421+00:00
-- url     : https://prove2.me/theorems/4b11398c-2988-4a3b-9838-ddfecc8ccaf6
-- title:
--   Subspaces of $\mathbb F_q^n$ of dimension at most $k$
-- statement:
--   For a field $\mathbb F$ (in the paper $\mathbb F_q$) and natural numbers $n,k$, this is the set
--   $$\{W\le \mathbb F^n:\ \dim W\le k\},$$
--   the index set of the tables of the truncated containment matrix $Z_{n,k}$. For $k\ge n$ it is the whole subspace lattice $\mathrm{Gr}_q(n)$. A table on it is a function $f:\{W\le\mathbb F^n:\dim W\le k\}\to R$.
--
--   **Formalization Note** $\mathbb F^n$ is `Fin n → F`, subspaces are `Submodule`s and dimension is `Module.finrank`. For a finite field the type is finite and carries a (noncomputable) `Fintype` instance.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, pp.1–2 (truncated containment matrix, "both indices have dimension at most k")

import Mathlib

namespace SubspaceConv

/-- The subspaces of `F^n` of dimension at most `k`: the index set of the tables of the
truncated transform `Z_{n,k}` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, p.1–2).

**Formalization Note** `F^n` is `Fin n → F` and dimension is `Module.finrank`. For `k ≥ n`
this is the set of all subspaces (the cutoff is clipped automatically). For a finite field the
type is finite, and a `Fintype` instance is provided noncomputably. -/
abbrev SubLE (F : Type*) [Field F] (n k : ℕ) : Type _ :=
  {W : Submodule F (Fin n → F) // Module.finrank F W ≤ k}

noncomputable instance (F : Type*) [Field F] [Finite F] (n k : ℕ) : Fintype (SubLE F n k) :=
  Fintype.ofFinite _

end SubspaceConv


