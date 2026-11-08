-- Prove2me | Definitions.Def_RepellingPairs_OSInstance
-- name    : RepellingPairs_OSInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:06.492438+00:00
-- url     : https://prove2.me/theorems/1ce54f4f-a305-47e9-b1ff-b914cfa32432
-- title:
--   Okamura-Seymour instance with terminals in boundary order
-- statement:
--   An **Okamura-Seymour instance** $(G,T)$ is a multigraph embedded in a closed disk together with terminals on the boundary circle. Here there are $k$ terminals $t_0,\dots,t_{k-1}$, and $t_i$ sits at the point $e^{\mathrm i\theta_i}$ with
--
--   $$
--   0\le\theta_0<\theta_1<\dots<\theta_{k-1}<2\pi .
--   $$
--
--   So the prescribed cyclic order of the terminals is the cyclic order of the indices. Other vertices may also lie on the boundary.
--
--   **Formalization Note** Increasing angle runs counterclockwise while §3.1 labels points clockwise. This is a mirror image, and every condition used with this order is invariant under reflection.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.5

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_DiskEmbedding

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- An Okamura-Seymour instance `(G, T)` with `k` terminals: "a pair (G, T) in which G is embedded in a
closed disk and all terminals lie on its boundary. Other graph vertices may also lie on the boundary."
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.5.

**Formalization Note.** The terminals are indexed by `Fin k` in their boundary order: `term i` sits at
angle `θ i`, with `θ` strictly increasing in `[0, 2π)`. So the prescribed cyclic order of `T` is the
cyclic order of `Fin k`. Increasing angle is counterclockwise; the page's "clockwise" labels of §3.1
are a mirror image, and every condition used with this order is invariant under reflection. Distinct
indices give distinct terminals, because `θ` is injective, `exp (θ i)` is injective on `[0, 2π)` and
positions are injective. -/
structure OSInstance (V : Type u) (E : Type v) (k : ℕ) where
  /-- The graph `G`. -/
  graph : Multigraph V E
  /-- Its embedding in the closed unit disk. -/
  emb : DiskEmbedding graph
  /-- The terminals, in boundary order. -/
  term : Fin k → V
  /-- The angle of each terminal. -/
  θ : Fin k → ℝ
  θ_strictMono : StrictMono θ
  θ_nonneg : ∀ i, 0 ≤ θ i
  θ_lt_two_pi : ∀ i, θ i < 2 * Real.pi
  pos_term : ∀ i, emb.pos (term i) = Complex.exp ((θ i : ℂ) * Complex.I)

end RepellingPairs


