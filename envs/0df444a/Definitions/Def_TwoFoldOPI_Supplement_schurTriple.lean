-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_schurTriple
-- name    : TwoFoldOPI_Supplement_schurTriple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:55:57.555144+00:00
-- url     : https://prove2.me/theorems/0515d79f-3879-413f-9ed0-1c8c4baceafd
-- title:
--   The Schur product code $V*E^{*2}$
-- statement:
--   For codes $V,E\subseteq\mathbb F_q^m$, $V*E^{*2}$ is the linear span of all coordinate-wise products $u\odot e\odot e'$ with $u\in V$ and $e,e'\in E$.
--
--   Orthogonality of $h$ to this code is an input condition of Algorithm 8.1.
--
--   **Formalization Note** By bilinearity, the span of triple products equals $V*(E*E)$ of Definition 5.23.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.23, p. 26; §8.1, Algorithm 8.1, p. 45

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The Schur product code `V ∗ E^{∗2}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.23, p.26: "For codes C_1, …, C_k ⊆ F_q^M, let C_1 ∗ ⋯ ∗ C_k ⊆ F_q^M denote
the linear subspace spanned by the coordinate-wise products c_1 ⊙ ⋯ ⊙ c_k with c_j ∈ C_j for every
j. When C_1 = ⋯ = C_k = C, we write C^{∗k}"; Algorithm 8.1, p.45 ("h ⊥ V ∗ E^{∗2}").

`schurTriple V E` is the span of all coordinate-wise products `u ⊙ e ⊙ e'` with `u ∈ V`,
`e, e' ∈ E`, i.e. `V ∗ E ∗ E = V ∗ E^{∗2}`.

**Formalization Note.** `V ∗ E^{∗2}` is the span of `u ⊙ x` with `x` in the span of products
`e ⊙ e'`; by bilinearity it equals the span of the triple products used here. -/
def schurTriple {K : Type*} [Field K] {m : ℕ} (V E : Submodule K (Fin m → K)) :
    Submodule K (Fin m → K) :=
  Submodule.span K {x | ∃ u ∈ V, ∃ e ∈ E, ∃ e' ∈ E, x = u * e * e'}

end Supplement

end TwoFoldOPI


