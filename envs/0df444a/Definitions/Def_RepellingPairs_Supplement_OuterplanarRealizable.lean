-- Prove2me | Definitions.Def_RepellingPairs_Supplement_OuterplanarRealizable
-- name    : RepellingPairs_Supplement_OuterplanarRealizable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:57:19.888446+00:00
-- url     : https://prove2.me/theorems/8e2548b2-8e08-43df-8b8e-cd32c9876629
-- title:
--   Outerplanar metrics: realizable by a disk-embedded graph with every vertex on the boundary
-- statement:
--   Let $T$ be a finite set of terminals and $D:T\times T\to\mathbb R$. The metric $D$ is **outerplanar** if there is an **outerplanar realization** of it: a finite multigraph $G$ embedded in a closed disk with **every** vertex of $G$ on the boundary circle, an injective placement of the terminals at vertices of $G$, and nonnegative edge lengths $\ell$ such that
--
--   $$
--   \mathrm{dist}_G(s,t)=D(s,t)\qquad\text{for all } s,t\in T .
--   $$
--
--   Vertices of $G$ that are not terminals (Steiner vertices) are allowed, edges may have length zero, and edges are arcs of the disk that may run through its interior. No order of the terminals around the circle is prescribed.
--
--   This is the class of metrics of §1.2 of the paper; Theorem 2 shows that it has no characterization by a bounded number of terminals.
--
--   **Formalization Note** The terminal set is an arbitrary finite type, so that the restriction of a metric to a subset of its terminals is again an instance. The graph is the base mission's multigraph with its disk embedding (parallel edges and loops allowed), and the distance is the base mission's $\mathrm{dist}_G$ with values in $[0,\infty]$; the condition is $\mathrm{dist}_G(s,t)=\max(D(s,t),0)$ read in $[0,\infty]$, which for a metric is $D(s,t)$.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.5 (PDF p.6): definitions of a realization and of an outerplanar realization; §1.2, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_PathLength
import Definitions.Def_RepellingPairs_DiskEmbedding

set_option autoImplicit false

namespace RepellingPairs

namespace Supplement

/-- A metric `D` on a finite terminal set `ι` is **outerplanar** if some outerplanar graph realizes it:
there are a finite multigraph `G`, an embedding of `G` in the closed unit disk with **every** vertex on the
boundary circle, distinct terminal vertices `τ a` (`a : ι`), and nonnegative edge lengths `ℓ` with
`dist_G(τ a, τ b) = D(a, b)` for all terminals `a, b`.
Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23,
2026), §2, p.5 ("An outerplanar realization is an OS realization in which every graph vertex lies on the
boundary"; "G realizes a metric D on T if distG(s, t) = D(s, t) for all s, t ∈ T. Steiner vertices in
V(G) \ T are allowed").

**Formalization Note.** The terminal set is an arbitrary finite type, so that the restriction of a metric
to a subset of its terminals (Theorem 2) is again an instance. No cyclic order of the terminals is
prescribed: the terminals may sit on the circle in any order. Parallel edges, loops, zero-length edges and
Steiner vertices are allowed; edges are arcs of the disk and may run through its interior. The vertex and
edge types live in `Type`, which loses nothing for finite graphs. -/
def OuterplanarRealizable {ι : Type} (D : ι → ι → ℝ) : Prop :=
  ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (G : Multigraph V E) (emb : DiskEmbedding G)
    (τ : ι → V) (ℓ : E → ℝ),
    (∀ v, ‖emb.pos v‖ = 1) ∧ (∀ e, 0 ≤ ℓ e) ∧ Function.Injective τ ∧
      ∀ a b, G.distG ℓ (τ a) (τ b) = ENNReal.ofReal (D a b)

end Supplement

end RepellingPairs


