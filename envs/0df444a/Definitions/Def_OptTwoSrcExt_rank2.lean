-- Prove2me | Definitions.Def_OptTwoSrcExt_rank2
-- name    : OptTwoSrcExt_rank2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:29.56395+00:00
-- url     : https://prove2.me/theorems/c78a203b-140d-4868-bc51-adcb37575f07
-- title:
--   Binary rank $\mathrm{rank}_2 h$ of a Boolean kernel
-- statement:
--   For finite sets $\alpha,\beta$ and a Boolean kernel $h:\alpha\times\beta\to\mathbb F_2$, the **binary rank** $\mathrm{rank}_2 h$ is the rank over $\mathbb F_2$ of the $|\alpha|\times|\beta|$ matrix of its $0/1$ values $(h(a,b))_{a,b}$, equivalently the $\mathbb F_2$-dimension of the span of its rows $h(a,\cdot)\in\mathbb F_2^{\beta}$. It is not the real rank of the sign matrix $((-1)^{h(a,b)})$.
--
--   The paper uses it for low-rank characters: a function of separation length $r$ over $\mathbb F_{2^\ell}$ has absolute-trace characters of binary rank at most $r\ell$, and the dispersion upgrade (Corollary 2.20) turns low binary rank plus dispersion into extraction.
--
--   **Formalization Note** The rank is the $\mathbb F_2$-dimension of the row span (`Module.finrank` of `Submodule.span`), which equals `Matrix.rank` over `ZMod 2` and needs no `Fintype` instance on the index types. Every use has finite index types; on an infinite row index an infinite-dimensional span would give the junk value $0$.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), §2 Notation and conventions, p.13 (PDF p.15)

import Mathlib

namespace OptTwoSrcExt

/-- **Binary rank of a Boolean kernel, `rank₂ h`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), §2 "Notation and conventions", printed p.13 (PDF p.15):
"Unless another field is specified, vector-space spans, dimensions, codimensions, orthogonality, and
matrix ranks are over F2. The notation rank2 h for a Boolean kernel means the rank of its matrix of
0/1 values, not the real rank of its sign matrix."

`rank2 h` is the dimension over `𝔽₂ = ZMod 2` of the span of the rows `h a : β → 𝔽₂`, that is, the
row rank (= rank) over `𝔽₂` of the matrix `(h a b)_{a, b}`.

**Formalization Note.** The rank is computed as the `𝔽₂`-dimension of the row space, which equals
`Matrix.rank` of the `0/1` table over `ZMod 2` and needs no `Fintype` instance on the index types
(the finite field `GaloisField 2 N` has only a `Finite` instance). Every use in this mission has
finite index types, where the row space is finite-dimensional; on an infinite row index the span
could be infinite-dimensional and `Module.finrank` would return the junk value `0`. -/
noncomputable def rank2 {α β : Type*} (h : α → β → ZMod 2) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range h))

end OptTwoSrcExt


