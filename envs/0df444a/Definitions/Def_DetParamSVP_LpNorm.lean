-- Prove2me | Definitions.Def_DetParamSVP_LpNorm
-- name    : DetParamSVP_LpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:36.9058+00:00
-- url     : https://prove2.me/theorems/15fa8463-efa6-4778-b12c-4e6b0a61d488
-- title:
--   The $\ell_p$ norm of an integer vector and its $p$-th power
-- statement:
--   For a finite index set $\iota$, an integer vector $v\in\mathbb Z^\iota$ and a real $p\ge1$,
--
--   $$\|v\|_p^p=\sum_{z\in\iota}|v_z|^p,\qquad \|v\|_p=\Big(\sum_{z\in\iota}|v_z|^p\Big)^{1/p}.$$
--
--   The norm measures lattice vectors in the shortest and closest vector problems; its $p$-th power is the quantity $W$ bounds in the definition of a locally dense lattice.
--
--   **Formalization Note** Both powers are real powers (`Real.rpow`); for $p\ge1$, $0^p=0$. The paper's vectors are integer vectors, cast to $\mathbb R$ entrywise.
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), §2.1, p.10 (ℓ_p norm), Definition 3.1(iii), p.17

import Mathlib

set_option autoImplicit false

namespace DetParamSVP

/-- The `p`-th power of the `ℓ_p` norm of an integer vector, `‖v‖_p^p = ∑_z |v_z|^p`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), §2.1, p.10, and
Definition 3.1(iii), p.17 ("W bounds the pth power of the norm").

**Formalization Note.** `|v_z|^p` is `Real.rpow`; for `p ≥ 1` (the only case the paper uses)
`0 ^ p = 0`. The index type is any finite type. -/
noncomputable def lpPowSum (p : ℝ) {ι : Type*} [Fintype ι] (v : ι → ℤ) : ℝ :=
  ∑ i, |((v i : ℤ) : ℝ)| ^ p

/-- The **`ℓ_p` norm** of an integer vector, `‖v‖_p = (∑_z |v_z|^p)^{1/p}` for `1 ≤ p < ∞`.

Hirahara–Lin–Liu–Ogitsuka (manuscript sha256 4584f5e2…), §2.1, p.10: "For a real vector,
∥v∥p = (∑ z |vz|p)1/p for 1 ≤ p < ∞".

**Formalization Note.** Both powers are `Real.rpow`. The vectors of the paper's lattices are
integer vectors, so the argument is `ι → ℤ`, cast to `ℝ` entrywise. -/
noncomputable def lpNorm (p : ℝ) {ι : Type*} [Fintype ι] (v : ι → ℤ) : ℝ :=
  lpPowSum p v ^ (1 / p)

end DetParamSVP


