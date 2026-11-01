-- Prove2me | Definitions.Def_NeebLieExt_HasKernel
-- name    : NeebLieExt_HasKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:25.731991+00:00
-- url     : https://prove2.me/theorems/c4f0a472-3f23-4f79-809b-80935a90d3dc
-- title:
--   Extensions with continuous $\mathfrak g$-kernel $[S]$ ($\mathrm{Ext}(\mathfrak g,\mathfrak n)_{[S]}$)
-- statement:
--   Two continuous outer actions are equivalent, $S\sim S'$, if $S=S'+\operatorname{ad}\circ\gamma$ for some $\gamma\in\mathrm{Lin}(\mathfrak g,\mathfrak n)$; the class $[S]$ is a **continuous $\mathfrak g$-kernel**. A topologically split extension $\mathfrak n\overset{\iota}{\hookrightarrow}\widehat{\mathfrak g}\overset{q}{\twoheadrightarrow}\mathfrak g$ **has $\mathfrak g$-kernel $[S]$** if for some continuous linear section $\sigma$ of $q$ the outer action $S_\sigma(x):=\operatorname{ad}(\sigma(x))|_{\mathfrak n}$ satisfies $S_\sigma=S+\operatorname{ad}\circ\gamma$ for a continuous linear $\gamma\colon\mathfrak g\to\mathfrak n$, i.e.
--   $$
--   \iota\big(S(x).m+[\gamma(x),m]\big)=[\sigma(x),\iota(m)]\qquad(x\in\mathfrak g,\ m\in\mathfrak n).
--   $$
--   $\mathrm{Ext}(\mathfrak g,\mathfrak n)_{[S]}$ is the set of classes of such extensions.
--
--   **Formalization Note** The identity is written through $\iota$, so no inverse of $\iota$ is needed. Any two continuous linear sections of a topologically split extension differ by a continuous linear map into $\iota(\mathfrak n)$, so "some section" and "every section" define the same class.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition II.2, p. 11 ("S ∼ S′ ⟺ (∃γ ∈ Lin(g, n)) S = S′ + ad_n ∘ γ"); the outer action S(x) := ad(σ(x))|_n of an extension, p. 10

import Mathlib

namespace NeebLieExt

/-- **The continuous g-kernel of an extension is `[S]`** (membership in `Ext(g, n)_[S]`). Neeb,
arXiv:math/0411256v1, Definition II.2, p. 11: "S ∼ S′ ⟺ (∃γ ∈ Lin(g, n)) S = S′ + ad_n ∘ γ. We
write [S] for the equivalence class of S, which we call a continuous g-kernel"; the outer action
of an extension is `S_σ(x) := ad(σ(x))|_n` for a continuous linear section `σ` (p. 10).

`HasKernel ι q S` says: there are a continuous linear section `σ` of `q` and a continuous linear
`γ : g → n` with `ι(S(x).m + ⁅γ(x), m⁆) = ⁅σ(x), ι(m)⁆` for all `x, m`, i.e.
`S_σ = S + ad ∘ γ`, so the extension's continuous g-kernel `[S_σ]` is `[S]`.

**Formalization Note** The identity is written through `ι`, so no inverse of `ι` is needed. For a
topologically split extension any two continuous linear sections differ by a continuous map into
`ι(n)`, so "some section" and "every section" give the same class. -/
def HasKernel {K n g E : Type*} [CommRing K] [LieRing n] [LieAlgebra K n] [LieRing g]
    [LieAlgebra K g] [LieRing E] [LieAlgebra K E] [TopologicalSpace n] [TopologicalSpace g]
    [TopologicalSpace E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g)
    (S : g →ₗ[K] LieDerivation K n n) : Prop :=
  ∃ σ : g →L[K] E, (∀ x, q (σ x) = x) ∧
    ∃ γ : g →L[K] n, ∀ x m, ι (S x m + ⁅γ x, m⁆) = ⁅σ x, ι m⁆

end NeebLieExt


