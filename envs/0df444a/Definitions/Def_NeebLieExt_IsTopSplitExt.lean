-- Prove2me | Definitions.Def_NeebLieExt_IsTopSplitExt
-- name    : NeebLieExt_IsTopSplitExt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:22.364555+00:00
-- url     : https://prove2.me/theorems/203dc573-20ae-4821-9e0b-5e1e85869fbe
-- title:
--   Topologically split extensions $\mathfrak n\hookrightarrow\widehat{\mathfrak g}\twoheadrightarrow\mathfrak g$
-- statement:
--   Let $\widehat{\mathfrak g}$ be a topological Lie algebra and $\iota\colon\mathfrak n\to\widehat{\mathfrak g}$, $q\colon\widehat{\mathfrak g}\to\mathfrak g$ homomorphisms of Lie algebras. The sequence $\mathfrak n\overset{\iota}{\hookrightarrow}\widehat{\mathfrak g}\overset{q}{\twoheadrightarrow}\mathfrak g$ is a **topologically split extension** of $\mathfrak g$ by $\mathfrak n$ if
--
--   1. $\iota$ and $q$ are continuous and $\iota$ is injective,
--   2. $\ker q=\iota(\mathfrak n)$, and
--   3. there is a continuous linear section $\sigma\colon\mathfrak g\to\widehat{\mathfrak g}$ of $q$ ($q\circ\sigma=\mathrm{id}_{\mathfrak g}$) such that
--   $$
--   \mathfrak n\times\mathfrak g\to\widehat{\mathfrak g},\qquad (n,x)\mapsto\iota(n)+\sigma(x)
--   $$
--   is a homeomorphism.
--
--   This is the paper's notion: $\mathfrak n$ is a topologically split ideal of $\widehat{\mathfrak g}$ with $\widehat{\mathfrak g}/\mathfrak n\cong\mathfrak g$ as topological vector spaces.
--
--   **Formalization Note** The paper's section $\widehat{\mathfrak g}/\mathfrak n\to\widehat{\mathfrak g}$ is composed with the identification $\widehat{\mathfrak g}/\mathfrak n\cong\mathfrak g$ induced by $q$. The homeomorphism implies that $\iota(\mathfrak n)$ is closed, that $q$ is open, and that $\widehat{\mathfrak g}$ is Hausdorff, so these are not assumed separately; continuity of $\iota,q$ and injectivity of $\iota$ also follow from it and are listed as part of "short exact sequence of topological Lie algebras".
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition II.1, p. 10 ("A topologically split short exact sequence n ↪ ĝ ↠ g is called a (topologically split) extension of g by n"); split subspaces and morphisms, p. 4

import Mathlib

namespace NeebLieExt

/-- **Topologically split extensions of `g` by `n`**. Neeb, arXiv:math/0411256v1, Definition II.1,
p. 10: "A topologically split short exact sequence n ↪ ĝ ↠ g is called a (topologically split)
extension of g by n. If we identify n with its image in ĝ, this means that ĝ is a Lie algebra
containing n as a topologically split ideal such that ĝ/n ≅ g."; "split" is defined on p. 4: "A
subspace W of a topological vector space V is called (topologically) split if it is closed and
there is a continuous linear map σ: V/W → V for which the map W × V/W → V, (w, x) ↦ w + σ(x) is an
isomorphism of topological vector spaces."

For Lie homomorphisms `ι : n → E` and `q : E → g`, `IsTopSplitExt ι q` says: `ι` and `q` are
continuous, `ι` is injective, `ker q = im ι`, and there is a continuous linear section `σ` of `q`
such that `n × g → E, (a, x) ↦ ι(a) + σ(x)` is a homeomorphism.

**Formalization Note** The quotient `E/ι(n)` is identified with `g` through `q`, so the paper's
section `V/W → V` becomes a section `g → E` of `q`. The homeomorphism makes `ι(n)` closed and
`q` open (it identifies `q` with the projection `n × g → g`), which is the paper's "ĝ/n ≅ g" as
topological vector spaces; the continuity of `ι` and `q` and the injectivity of `ι` are also
consequences of it, and are listed because they are part of "short exact sequence of
topological Lie algebras". The Hausdorff property of `E` follows from the homeomorphism with
`n × g` and is not assumed separately. -/
def IsTopSplitExt {K n g E : Type*} [CommRing K] [LieRing n] [LieAlgebra K n] [LieRing g]
    [LieAlgebra K g] [LieRing E] [LieAlgebra K E] [TopologicalSpace n] [TopologicalSpace g]
    [TopologicalSpace E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g) : Prop :=
  Continuous ι ∧ Continuous q ∧ Function.Injective ι ∧ (∀ e, q e = 0 ↔ e ∈ Set.range ι) ∧
    ∃ σ : g →L[K] E, (∀ x, q (σ x) = x) ∧ IsHomeomorph (fun p : n × g => ι p.1 + σ p.2)

end NeebLieExt


