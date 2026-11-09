-- Prove2me | Definitions.Def_RSSubspaceDesign_ratRank
-- name    : RSSubspaceDesign_ratRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:35.140416+00:00
-- url     : https://prove2.me/theorems/748f9bf6-d5e4-400f-b26f-88d4e1ee6f14
-- title:
--   The $K(X)$-rank $\dim_{K(X)}\operatorname{span}_{K(X)}S$ of a set of polynomials
-- statement:
--   For a field extension $F/K$ and a set $S\subseteq F[X]$,
--   $$\rho(S)=\dim_{K(X)}\operatorname{span}_{K(X)}(S),$$
--   the dimension over $K(X)$ of the $K(X)$-span of $S$ inside $F(X)$.
--
--   Proposition 4.3 bounds the ranks $t=\rho(W)$ and $t_i=\rho(W_i)$ of a polynomial space and of its coordinate kernels.
--
--   **Formalization Note** For finite $F/K$ the span has dimension at most $[F:K]$, so the dimension is finite.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Proposition 4.3, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra

open Polynomial

namespace RSSubspaceDesign

/-- **The `K(X)`-rank of a set of polynomials.** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Proposition 4.3, p.19: for `S ⊆ F[X]`,
`ρ(S) = dim_{K(X)} span_{K(X)}(S)`, the span taken inside `F(X)`.

**Formalization Note.** `S` is mapped into `F(X) = RatFunc F` by `algebraMap F[X] (RatFunc F)`, and
`F(X)` is a `K(X)`-vector space through `ratFuncAlgebra K F`. For finite `F/K` the span has
dimension at most `[F : K]`, so `Module.finrank` takes no junk value there. -/
noncomputable def ratRank (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Set F[X]) : ℕ :=
  letI := ratFuncAlgebra K F
  Module.finrank (RatFunc K) (Submodule.span (RatFunc K) (algebraMap F[X] (RatFunc F) '' S))

end RSSubspaceDesign


