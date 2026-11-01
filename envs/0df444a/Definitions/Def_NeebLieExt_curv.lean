-- Prove2me | Definitions.Def_NeebLieExt_curv
-- name    : NeebLieExt_curv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:23.922836+00:00
-- url     : https://prove2.me/theorems/247be58d-e201-4147-ab73-35aef7c4400a
-- title:
--   The curvature $R_S$ and the condition $R_S=\operatorname{ad}\circ\omega$
-- statement:
--   For a linear map $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$, the **curvature** of $S$ is
--   $$
--   R_S(x,y)=[S(x),S(y)]-S([x,y])\in\operatorname{der}\mathfrak n,\qquad x,y\in\mathfrak g,
--   $$
--   so that $R_S(x,y).m=S(x).S(y).m-S(y).S(x).m-S([x,y]).m$. For $\omega\colon\mathfrak g\times\mathfrak g\to\mathfrak n$, the condition **$R_S=\operatorname{ad}\circ\omega$** means
--   $$
--   R_S(x,y).m=[\omega(x,y),m]\qquad\text{for all } x,y\in\mathfrak g,\ m\in\mathfrak n .
--   $$
--
--   $S$ is a homomorphism of Lie algebras exactly when $R_S=0$. The condition $R_S=\operatorname{ad}\circ\omega$ says that $S$ fails to be a homomorphism only by inner derivations, and is the first half of the definition of a factor system.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Proposition I.5, p. 7 ("R_S(x, y) = [S(x), S(y)] − S([x, y])"); Definition II.2, p. 11 (R_S = ad ∘ ω)

import Mathlib

namespace NeebLieExt

/-- **Curvature** `R_S`. Neeb, arXiv:math/0411256v1, Proposition I.5, p. 7: "Let
R_S(x, y) = [S(x), S(y)] − S([x, y]) for x, y ∈ g."

`curv S x y m = S(x)(S(y)m) − S(y)(S(x)m) − S([x, y])m`, i.e. `R_S(x, y)` applied to `m ∈ n`. -/
def curv {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n] [LieAlgebra K n]
    (S : g →ₗ[K] LieDerivation K n n) (x y : g) (m : n) : n :=
  S x (S y m) - S y (S x m) - S ⁅x, y⁆ m

/-- **The condition `R_S = ad ∘ ω`**. Neeb, arXiv:math/0411256v1, Definition II.2, p. 11.

`CurvEqAd S ω` says `R_S(x, y) = ad(ω(x, y))` on `n` for all `x, y ∈ g`, i.e.
`curv S x y m = ⁅ω x y, m⁆` for all `x, y, m`.

**Formalization Note** Companion of `curv` in the same module. -/
def CurvEqAd {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) : Prop :=
  ∀ x y m, curv S x y m = ⁅ω x y, m⁆

end NeebLieExt


