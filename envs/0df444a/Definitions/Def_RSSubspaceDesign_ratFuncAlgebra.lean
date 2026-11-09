-- Prove2me | Definitions.Def_RSSubspaceDesign_ratFuncAlgebra
-- name    : RSSubspaceDesign_ratFuncAlgebra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:18.656121+00:00
-- url     : https://prove2.me/theorems/7c94f219-219b-4476-8724-5afc218d88d4
-- title:
--   The $K(X)$-algebra structure on $F(X)$
-- statement:
--   For a field extension $F/K$, the field of rational functions $F(X)$ is an algebra over $K(X)$ through the inclusion $K(X)\hookrightarrow F(X)$ that applies $K\hookrightarrow F$ to the coefficients of numerator and denominator and fixes $X$.
--
--   This is the setting $L=K(X)$ acting on $F(X)$ of Corollary 2.16, Lemma 2.20 and Proposition 4.3, where ranks of sets of polynomials are measured over $K(X)$.
--
--   **Formalization Note** Mathlib has no such instance; it is a definition installed locally in each statement that uses it.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Section 2.2, p.13 and Corollary 2.16, p.14 (PDF pp.15–16)

import Mathlib

open Polynomial

namespace RSSubspaceDesign

/-- **The `K(X)`-structure on `F(X)`.** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version,
sha256 cf26424b…f36206), Section 2.2, p.13 and Corollary 2.16, p.14 (`L = K(X)` acting on `F(X)`).

For a field extension `F/K`, the field `F(X)` of rational functions is a `K(X)`-algebra through the
map `K(X) → F(X)` that applies `K → F` to the coefficients of numerator and denominator and fixes
`X`.

**Formalization Note.** Mathlib has no such instance; this is `RatFunc.mapRingHom` of
`Polynomial.mapRingHom (algebraMap K F)` as an algebra. It is a `def`, not a global instance, and
statements install it with `letI`. -/
@[instance_reducible]
noncomputable def ratFuncAlgebra (K F : Type*) [Field K] [Field F] [Algebra K F] :
    Algebra (RatFunc K) (RatFunc F) :=
  (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap K F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap K F).injective))).toAlgebra

end RSSubspaceDesign


