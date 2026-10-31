-- Prove2me | Definitions.Def_MixedManna_IsLemkePath
-- name    : MixedManna_IsLemkePath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:53.629211+00:00
-- url     : https://prove2.me/theorems/17d96cb5-ce7f-4428-896c-1d7e5ce2a770
-- title:
--   Path of Algorithm 1 (Lemke's scheme) from the primary ray
-- statement:
--   A **path of Algorithm 1** of length $T$ is a sequence $w_0,w_1,\dots,w_T$ of points with
--
--   1. $w_0=S_0$;
--   2. every $w_t$ a vertex of $\mathcal P$;
--   3. the $w_t$ pairwise distinct;
--   4. the closed segment $[w_t,w_{t+1}]$ contained in the solution set of LCP (14) for every $t<T$;
--   5. $z(w_t)>0$ for every $t<T$.
--
--   Algorithm 1 pivots at the double label of the current vertex and travels along the corresponding edge of $\mathcal P$, inside the solution set, to the next vertex, while $z>0$; Lemke's scheme never repeats a vertex. At a nondegenerate vertex the two edges of the solution set are the two ways to relax the double label, so under the nondegeneracy hypothesis the paths from $S_0$ are the vertex sequences Algorithm 1 visits. "Algorithm 1 reaches a vertex $v$" means $v=w_T$ for such a path.
--
--   **Formalization Note** The path is a function on $\mathbb N$ read up to $T$.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §2.2 p.6 (Lemke's scheme, primary ray, never repeats a vertex) and Algorithm 1, p.23

import Mathlib
import Definitions.Def_MixedManna_lcpSolutions
import Definitions.Def_MixedManna_primaryStart

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **A path of Algorithm 1 from the primary ray** (Chaudhury, Garg, McGlaughlin, Mehta,
*Competitive Allocation of a Mixed Manna*, arXiv:2008.02753v1, §2.2 p.6 and Algorithm 1, p.23):
a sequence `w₀, w₁, …, w_T` with

1. `w₀ = S₀`, the start of the primary ray;
2. every `w_t` a vertex (extreme point) of `𝒫`;
3. the `w_t` pairwise distinct ("never repeats a vertex", p.6);
4. the closed segment `[w_t, w_{t+1}]` contained in the solution set `S` of LCP (14) for every
   `t < T` (the edge of `S` traveled by a pivot);
5. `z(w_t) > 0` for every `t < T` (the loop `while z > 0`).

**Formalization Note** Algorithm 1 pivots at the double label and moves along an edge of `𝒫`
inside `S` to the next vertex (p.6, p.22). At a nondegenerate vertex the two edges of `S` are the
two ways of relaxing the double label, and a segment of `S` between two vertices cannot pass
through a third, so under the hypothesis `NondegenerateInRegion` the paths from `S₀` that stay
in the region `p < P`, `r < R` are the vertex sequences Algorithm 1 visits. "Algorithm 1 reaches a
vertex with property Φ" is "some path has `Φ (w T)`". The path is `w : ℕ → LCPVar I`, read up to
`T`. -/
def IsLemkePath (I : Instance N M) (P R : ℝ) (δ : M → ℝ) (ε : ℝ) (w : ℕ → LCPVar I) (T : ℕ) :
    Prop :=
  w 0 = primaryStart I P R ∧
  (∀ t ≤ T, w t ∈ Set.extremePoints ℝ (lcpPolyhedron I P R δ ε)) ∧
  (∀ t ≤ T, ∀ t' ≤ T, w t = w t' → t = t') ∧
  (∀ t < T, segment ℝ (w t) (w (t + 1)) ⊆ lcpSolutions I P R δ ε) ∧
  (∀ t < T, 0 < zv (w t))

end MixedManna


