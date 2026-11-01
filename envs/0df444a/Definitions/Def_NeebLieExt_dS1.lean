-- Prove2me | Definitions.Def_NeebLieExt_dS1
-- name    : NeebLieExt_dS1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:25.865998+00:00
-- url     : https://prove2.me/theorems/ff362814-35f3-4db8-b943-32d0a83356f9
-- title:
--   The covariant differential $d_S$ in degrees $1$, $2$, $3$
-- statement:
--   For a linear map $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ the **covariant differential** of an $\mathfrak n$-valued $p$-cochain $\alpha$ is
--   $$
--   (d_S\alpha)(x_0,\dots,x_p)=\sum_{j=0}^{p}(-1)^j S(x_j).\alpha(x_0,\dots,\widehat{x_j},\dots,x_p)+\sum_{i<j}(-1)^{i+j}\alpha([x_i,x_j],x_0,\dots,\widehat{x_i},\dots,\widehat{x_j},\dots,x_p).
--   $$
--   The module spells this out for $p=1,2,3$; for instance
--   $$
--   (d_S\gamma)(x,y)=S(x).\gamma(y)-S(y).\gamma(x)-\gamma([x,y]),
--   $$
--   $$
--   (d_S\omega)(x,y,z)=S(x).\omega(y,z)-S(y).\omega(x,z)+S(z).\omega(x,y)-\omega([x,y],z)+\omega([x,z],y)-\omega([y,z],x).
--   $$
--
--   When $S$ is a homomorphism, $d_S$ is the Chevalley–Eilenberg differential of the $\mathfrak g$-module $\mathfrak n$; in general $d_S^2\neq0$. On $\mathfrak z(\mathfrak n)$-valued cochains it is the differential of the $\mathfrak g$-module $\mathfrak z(\mathfrak n)$ with $x.z:=S(x).z$.
--
--   **Formalization Note** The three degrees are separate functions `dS1`, `dS2`, `dS3`, defined on arbitrary functions of the right arity; the signs are those of the formula above, term by term.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Lemma I.4, p. 6 (the formula for d_S α); Definition II.2, p. 11 (x.z := S(x).z on z(n))

import Mathlib

namespace NeebLieExt

/-- **Covariant differential on 1-cochains**. Neeb, arXiv:math/0411256v1, Lemma I.4, p. 6:
"(d_S α)(x_0, …, x_p) := Σ_{j=0}^p (−1)^j S(x_j).α(x_0, …, x̂_j, …, x_p)
+ Σ_{i<j} (−1)^{i+j} α([x_i, x_j], x_0, …, x̂_i, …, x̂_j, …, x_p)", for `p = 1`:

`(d_S γ)(x, y) = S(x).γ(y) − S(y).γ(x) − γ([x, y])`.

**Formalization Note** `γ` is any function `g → n` (in use, a continuous linear map); the same formula is used for `z(n)`-valued cochains, where `g` acts by `x.z := S(x).z`
(Definition II.2, p. 11). -/
def dS1 {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n] [LieAlgebra K n]
    (S : g →ₗ[K] LieDerivation K n n) (γ : g → n) (x y : g) : n :=
  S x (γ y) - S y (γ x) - γ ⁅x, y⁆

/-- **Covariant differential on 2-cochains**. Neeb, arXiv:math/0411256v1, Lemma I.4, p. 6, for
`p = 2`:

`(d_S ω)(x, y, z) = S(x).ω(y, z) − S(y).ω(x, z) + S(z).ω(x, y)
 − ω([x, y], z) + ω([x, z], y) − ω([y, z], x)`.

**Formalization Note** Companion of `dS1`. The first three terms are the `j`-sum with sign
`(−1)^j`, the last three the `i < j`-sum with sign `(−1)^{i+j}` for `(i, j) = (0,1), (0,2), (1,2)`. -/
def dS2 {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n] [LieAlgebra K n]
    (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (x y z : g) : n :=
  S x (ω y z) - S y (ω x z) + S z (ω x y) - ω ⁅x, y⁆ z + ω ⁅x, z⁆ y - ω ⁅y, z⁆ x

/-- **Covariant differential on 3-cochains**. Neeb, arXiv:math/0411256v1, Lemma I.4, p. 6, for
`p = 3`:

`(d_S η)(x₀, x₁, x₂, x₃) = Σ_{j=0}^{3} (−1)^j S(x_j).η(…x̂_j…)
 + Σ_{i<j} (−1)^{i+j} η([x_i, x_j], …x̂_i…x̂_j…)`.

**Formalization Note** Companion of `dS1`. The ten terms are written out: four `j`-terms and six
`i < j`-terms for `(i, j) = (0,1), (0,2), (0,3), (1,2), (1,3), (2,3)` with signs `−, +, −, −, +, −`. -/
def dS3 {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n] [LieAlgebra K n]
    (S : g →ₗ[K] LieDerivation K n n) (η : g → g → g → n) (x₀ x₁ x₂ x₃ : g) : n :=
  S x₀ (η x₁ x₂ x₃) - S x₁ (η x₀ x₂ x₃) + S x₂ (η x₀ x₁ x₃) - S x₃ (η x₀ x₁ x₂)
    - η ⁅x₀, x₁⁆ x₂ x₃ + η ⁅x₀, x₂⁆ x₁ x₃ - η ⁅x₀, x₃⁆ x₁ x₂
    - η ⁅x₁, x₂⁆ x₀ x₃ + η ⁅x₁, x₃⁆ x₀ x₂ - η ⁅x₂, x₃⁆ x₀ x₁

end NeebLieExt


