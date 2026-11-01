-- Prove2me | Definitions.Def_NeebLieExt_gaugeS
-- name    : NeebLieExt_gaugeS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:16.999804+00:00
-- url     : https://prove2.me/theorems/7d9c1b41-35e8-4a24-ba2f-cfa76f13876e
-- title:
--   The gauge action $\gamma.(S,\omega)=(S+\operatorname{ad}\circ\gamma,\ \omega+d_S\gamma+\tfrac12[\gamma,\gamma])$
-- statement:
--   For a continuous linear map $\gamma\colon\mathfrak g\to\mathfrak n$ (an element of $C^1(\mathfrak g,\mathfrak n)=\mathrm{Lin}(\mathfrak g,\mathfrak n)$), a linear map $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ and $\omega\colon\mathfrak g\times\mathfrak g\to\mathfrak n$, put
--   $$
--   \gamma.(S,\omega):=\Big(S+\operatorname{ad}\circ\gamma,\ \ \omega+d_S\gamma+\tfrac12[\gamma,\gamma]\Big),
--   $$
--   that is, $(S+\operatorname{ad}\circ\gamma)(x).m=S(x).m+[\gamma(x),m]$ and
--   $$
--   \big(\omega+d_S\gamma+\tfrac12[\gamma,\gamma]\big)(x,y)=\omega(x,y)+(d_S\gamma)(x,y)+[\gamma(x),\gamma(y)].
--   $$
--
--   This is the change of the pair $(S,\omega)$ attached to an extension when its continuous section $\sigma$ is replaced by $\sigma+\gamma$; Theorem II.7 identifies extensions with orbits of this action.
--
--   **Formalization Note** The two components are `gaugeS S γ` and `gaugeω S ω γ`. $\tfrac12[\gamma,\gamma](x,y)=[\gamma(x),\gamma(y)]$ because the product of 1-cochains is $(\alpha\wedge\beta)(x,y)=[\alpha(x),\beta(y)]-[\alpha(y),\beta(x)]$ (p. 5); no division by $2$ occurs. The differential $d_S\gamma$ uses the original $S$.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Lemma I.9, p. 8 ("γ.(S, ω) := (S + ad ∘ γ, ω + d_S γ + 1/2[γ, γ])"); product formula, p. 5

import Mathlib
import Definitions.Def_NeebLieExt_dS1

namespace NeebLieExt

/-- **The gauge action on outer actions**, `S ↦ S + ad ∘ γ`. Neeb, arXiv:math/0411256v1,
Lemma I.9, p. 8: "the prescription γ.(S, ω) := (S + ad ∘ γ, ω + d_S γ + ½[γ, γ]) defines an action
of the abelian group C¹(g, n) on C¹_c(g, der n) × C²(g, n)".

For a continuous linear `γ : g → n` (`C¹(g, n) = Lin(g, n)`), `gaugeS S γ` is the linear map
`x ↦ S(x) + ad(γ(x))`, so `gaugeS S γ x m = S(x).m + ⁅γ(x), m⁆`. -/
def gaugeS {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (γ : g →L[K] n) : g →ₗ[K] LieDerivation K n n :=
  S + (LieDerivation.ad K n).toLinearMap ∘ₗ (γ : g →ₗ[K] n)

/-- **The gauge action on 2-cochains**, `ω ↦ ω + d_S γ + ½[γ, γ]`. Neeb, arXiv:math/0411256v1,
Lemma I.9, p. 8 (second component of `γ.(S, ω)`).

`gaugeω S ω γ x y = ω(x, y) + (d_S γ)(x, y) + ⁅γ(x), γ(y)⁆`.

**Formalization Note** Companion of `gaugeS`. The term `½[γ, γ](x, y)` is `⁅γ(x), γ(y)⁆`: by the
product formula on p. 5, `(α ∧_m β)(x, y) = m(α(x), β(y)) − m(α(y), β(x))`, so
`[γ, γ](x, y) = ⁅γ x, γ y⁆ − ⁅γ y, γ x⁆ = 2⁅γ x, γ y⁆`; no division by 2 occurs. The covariant
differential is taken with the *old* `S`, as on p. 8. -/
def gaugeω {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (γ : g →L[K] n) (x y : g) : n :=
  ω x y + dS1 S γ x y + ⁅γ x, γ y⁆

end NeebLieExt


