-- Prove2me | Definitions.Def_NeebLieExt_InZ2Center
-- name    : NeebLieExt_InZ2Center
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:09.314403+00:00
-- url     : https://prove2.me/theorems/82d87fe0-cafc-44b4-8579-e2da68496bb2
-- title:
--   $Z^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$, $B^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$ and $Z^3(\mathfrak g,\mathfrak z(\mathfrak n))_S$
-- statement:
--   Let $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ be linear; it makes the centre $\mathfrak z(\mathfrak n)$ a $\mathfrak g$-module by $x.z:=S(x).z$, with differential $d_S$.
--
--   1. $Z^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$ is the set of $\beta\in C^2(\mathfrak g,\mathfrak n)$ with values in $\mathfrak z(\mathfrak n)$ and $d_S\beta=0$.
--   2. $B^2(\mathfrak g,\mathfrak z(\mathfrak n))_S=d_S\,C^1(\mathfrak g,\mathfrak z(\mathfrak n))$ is the set of $\beta$ of the form $\beta=d_S\alpha$ for a continuous linear map $\alpha\colon\mathfrak g\to\mathfrak n$ with values in $\mathfrak z(\mathfrak n)$.
--   3. $Z^3(\mathfrak g,\mathfrak z(\mathfrak n))_S$ is the set of $\eta\in C^3(\mathfrak g,\mathfrak n)$ with values in $\mathfrak z(\mathfrak n)$ and $d_S\eta=0$.
--
--   The quotient $H^2(\mathfrak g,\mathfrak z(\mathfrak n))_S=Z^2/B^2$ is the translation group of the affine space of extension classes with outer action $[S]$ (Theorem II.7).
--
--   **Formalization Note** $\mathfrak z(\mathfrak n)$-valued cochains are $\mathfrak n$-valued cochains with central values; the predicates `InZ2Center`, `InB2Center`, `InZ3Center` describe the subsets, and $H^2$ is not built as a quotient.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition I.1, pp. 4–5 (Z^p, B^p); Definition II.2, p. 11 (x.z := S(x).z); Theorem II.7, p. 13

import Mathlib
import Definitions.Def_NeebLieExt_IsCochain2
import Definitions.Def_NeebLieExt_IsCentral
import Definitions.Def_NeebLieExt_dS1

namespace NeebLieExt

/-- **Cocycles `Z²(g, z(n))_S`**. Neeb, arXiv:math/0411256v1, Definition I.1 (p. 4) for the
topological g-module `z(n)` with `x.z := S(x).z` (Definition II.2, p. 11); used in Theorem II.7,
p. 13.

`InZ2Center S β` says that `β ∈ C²(g, n)` takes values in the centre `z(n)` and `d_S β = 0`.

**Formalization Note** `z(n)`-valued cochains are `n`-valued cochains with central values; the
differential is `dS2` with the same `S`, which on `z(n)` is the differential of the module
`x.z := S(x).z`. -/
def InZ2Center {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (β : g → g → n) : Prop :=
  IsCochain2 K β ∧ (∀ x y, IsCentral (β x y)) ∧ ∀ x y z, dS2 S β x y z = 0

/-- **Coboundaries `B²(g, z(n))_S`**. Neeb, arXiv:math/0411256v1, Definition I.1, p. 5
("B^p(g, V) := d_g(C^{p−1}(g, V))") for the module `z(n)` with `x.z := S(x).z`.

`InB2Center S β` says that `β = d_S α` for some continuous linear `α : g → n` with values in
`z(n)`.

**Formalization Note** Companion of `InZ2Center`. -/
def InB2Center {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (β : g → g → n) : Prop :=
  ∃ α : g →L[K] n, (∀ x, IsCentral (α x)) ∧ ∀ x y, β x y = dS1 S α x y

/-- **Cocycles `Z³(g, z(n))_S`**. Neeb, arXiv:math/0411256v1, Definition I.1, p. 4 (`p = 3`) for
the module `z(n)`; used in Lemma I.9(3), p. 8.

`InZ3Center S η` says that `η ∈ C³(g, n)` takes values in `z(n)` and `d_S η = 0`.

**Formalization Note** Companion of `InZ2Center`. -/
def InZ3Center {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (η : g → g → g → n) : Prop :=
  IsCochain3 K η ∧ (∀ x y z, IsCentral (η x y z)) ∧
    ∀ x₀ x₁ x₂ x₃, dS3 S η x₀ x₁ x₂ x₃ = 0

end NeebLieExt


