-- Prove2me | Definitions.Def_RepellingPairs_PathLength
-- name    : RepellingPairs_PathLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:17.89421+00:00
-- url     : https://prove2.me/theorems/e5717f59-23a1-434f-8c73-2938aee67a25
-- title:
--   Length of a walk, shortest paths, and the distance $\mathrm{dist}_G$
-- statement:
--   For edge lengths $\ell:E\to\mathbb R$ the **length** of a walk is the sum of $\ell$ over its edges, counted with multiplicity. A walk $p$ from $u$ to $w$ is **shortest** if no path from $u$ to $w$ is shorter. For nonnegative lengths the **distance** is
--
--   $$
--   \mathrm{dist}_G(u,w)=\inf\{\ell(p): p\text{ a path from }u\text{ to }w\}.
--   $$
--
--   Lemma 5 is stated with this distance.
--
--   **Formalization Note** The distance takes values in $[0,\infty]$, so that a pair with no path between them has distance $\infty$ rather than a default real value.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.5

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph

set_option autoImplicit false

namespace RepellingPairs

open scoped ENNReal

universe u v

namespace Multigraph

variable {V : Type u} {E : Type v} {G : Multigraph V E}

/-- The length of a walk under edge lengths `ℓ`, each edge counted with its multiplicity.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.5. -/
def Walk.len (ℓ : E → ℝ) {u w : V} (p : G.Walk u w) : ℝ := (p.edges.map ℓ).sum

/-- `p` is a shortest `u`-`w` path under `ℓ`: no path from `u` to `w` is shorter. -/
def Walk.IsShortest (ℓ : E → ℝ) {u w : V} (p : G.Walk u w) : Prop :=
  ∀ q : G.Path u w, p.len ℓ ≤ q.1.len ℓ

/-- The shortest-path distance `dist_G(u, w)` of §2, p.5, for nonnegative edge lengths.

**Formalization Note.** The value is in `ℝ≥0∞`: with no `u`-`w` path the infimum over the empty type
is `⊤`, the usual distance between disconnected vertices, not a junk `0`. For `ℓ ≥ 0` the infimum over
paths equals the infimum over walks. `ENNReal.ofReal` is the identity on the nonnegative lengths the
paper allows. -/
noncomputable def distG (G : Multigraph V E) (ℓ : E → ℝ) (u w : V) : ℝ≥0∞ :=
  ⨅ p : G.Path u w, ENNReal.ofReal (p.1.len ℓ)

end Multigraph

end RepellingPairs


