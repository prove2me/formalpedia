-- Prove2me | Definitions.Def_NeebLieExt_ExtEquivModel
-- name    : NeebLieExt_ExtEquivModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:11.91974+00:00
-- url     : https://prove2.me/theorems/66b16c5e-ffc2-4891-a154-380e3e52fde6
-- title:
--   Equivalence of an extension with a twisted product $\mathfrak n\times_{(S,\omega)}\mathfrak g$
-- statement:
--   1. An extension $\mathfrak n\overset{\iota}{\hookrightarrow}\widehat{\mathfrak g}\overset{q}{\twoheadrightarrow}\mathfrak g$ is **equivalent to $\mathfrak n\times_{(S,\omega)}\mathfrak g$** if there is a continuous linear map $\Phi\colon\mathfrak n\times\mathfrak g\to\widehat{\mathfrak g}$ that preserves brackets (the twisted bracket (2.1) on the source), with $\Phi(n,0)=\iota(n)$ and $q(\Phi(n,x))=x$; that is, a morphism of topological Lie algebras making the diagram with $\mathrm{id}_{\mathfrak n}$ and $\mathrm{id}_{\mathfrak g}$ commute.
--   2. Two twisted products are **equivalent**, $\mathfrak n\times_{(S,\omega)}\mathfrak g\sim\mathfrak n\times_{(S',\omega')}\mathfrak g$, if there is a continuous linear $\varphi\colon\mathfrak n\times\mathfrak g\to\mathfrak n\times\mathfrak g$ with $\varphi(n,0)=(n,0)$, $\varphi(n,x)\in\mathfrak n\times\{x\}$, and
--   $$
--   \varphi\big([p,p']_{(S,\omega)}\big)=[\varphi(p),\varphi(p')]_{(S',\omega')}.
--   $$
--
--   $\mathrm{Ext}(\mathfrak g,\mathfrak n)$ is the set of equivalence classes of extensions; these two relations are the instances of that equivalence used to state the classification.
--
--   **Formalization Note** The morphism goes from the twisted product to $\widehat{\mathfrak g}$ (resp. from $(S,\omega)$ to $(S',\omega')$); the paper observes that such a morphism is automatically an isomorphism of topological Lie algebras, so the direction is immaterial.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition II.1, p. 10 (equivalence of extensions); Lemma II.4, pp. 11–12 (the map Φ)

import Mathlib
import Definitions.Def_NeebLieExt_twistedBracket

namespace NeebLieExt

/-- **An extension is equivalent to the twisted product `n ×_(S,ω) g`**. Neeb,
arXiv:math/0411256v1, Definition II.1, p. 10: "Two extensions n ↪ ĝ₁ ↠ g and n ↪ ĝ₂ ↠ g are called
equivalent if there exists a morphism φ: ĝ₁ → ĝ₂ of topological Lie algebras such that the diagram
[with vertical maps id_n, φ, id_g] commutes"; Lemma II.4, p. 11–12 (the map Φ).

For an extension `n →ι E →q g`, `ExtEquivModel ι q S ω` says there is a continuous linear map
`Φ : n × g → E` with `Φ(a, 0) = ι(a)`, `q(Φ(a, x)) = x`, and
`Φ(twistedBracket S ω p p') = ⁅Φ p, Φ p'⁆`, i.e. a morphism of topological Lie algebras
`n ×_(S,ω) g → E` making the diagram commute.

**Formalization Note** The morphism goes from the model `n ×_(S,ω) g` to `E`. The paper notes
(p. 10, "Exercise") that such a morphism is an isomorphism, so equivalence is symmetric and the
direction is immaterial. -/
def ExtEquivModel {K n g E : Type*} [CommRing K] [LieRing n] [LieAlgebra K n] [LieRing g]
    [LieAlgebra K g] [LieRing E] [LieAlgebra K E] [TopologicalSpace n] [TopologicalSpace g]
    [TopologicalSpace E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g)
    (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) : Prop :=
  ∃ Φ : (n × g) →L[K] E, (∀ a, Φ (a, 0) = ι a) ∧ (∀ p, q (Φ p) = p.2) ∧
    ∀ p p', Φ (twistedBracket S ω p p') = ⁅Φ p, Φ p'⁆

/-- **Equivalence of two twisted products**. Neeb, arXiv:math/0411256v1, Definition II.1, p. 10,
for the extensions `n ×_(S,ω) g` and `n ×_(S′,ω′) g` of Lemma II.4.

`ModelEquiv S ω S' ω'` says there is a continuous linear `φ : n × g → n × g` with `φ(a, 0) = (a, 0)`,
`(φ p).2 = p.2`, and `φ(twistedBracket S ω p p') = twistedBracket S' ω' (φ p) (φ p')`.

**Formalization Note** Companion of `ExtEquivModel`: the same notion with the model
`n ×_(S′,ω′) g` (inclusion `a ↦ (a, 0)`, projection `p ↦ p.2`) in place of `E`. -/
def ModelEquiv {K n g : Type*} [CommRing K] [LieRing n] [LieAlgebra K n] [LieRing g]
    [LieAlgebra K g] [TopologicalSpace n] [TopologicalSpace g]
    (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n)
    (S' : g →ₗ[K] LieDerivation K n n) (ω' : g → g → n) : Prop :=
  ∃ φ : (n × g) →L[K] (n × g), (∀ a, φ (a, 0) = (a, 0)) ∧ (∀ p, (φ p).2 = p.2) ∧
    ∀ p p', φ (twistedBracket S ω p p') = twistedBracket S' ω' (φ p) (φ p')

end NeebLieExt


