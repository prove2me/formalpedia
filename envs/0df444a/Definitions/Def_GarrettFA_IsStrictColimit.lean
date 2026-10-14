-- Prove2me | Definitions.Def_GarrettFA_IsStrictColimit
-- name    : GarrettFA_IsStrictColimit
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:25:54.580558+00:00
-- url     : https://prove2.me/theorems/2145ea8b-1ecd-4269-ac50-96abc981afc1
-- title:
--   Strict (locally convex) colimit of a countable chain of subspaces
-- statement:
--   Let $V$ be a topological vector space over $\mathbb K=\mathbb R$ or $\mathbb C$ and let $V_0\subset V_1\subset V_2\subset\cdots$ be subspaces of $V$, each carrying the subspace topology. $V$ is the **strict (locally convex) colimit** of the $V_n$ if:
--
--   1. all containments $V_n\subsetneq V_{n+1}$ are proper;
--   2. $V=\bigcup_n V_n$;
--   3. each $V_n$ is closed in $V_{n+1}$;
--   4. $V$ is locally convex;
--   5. the topology of $V$ is the locally convex colimit topology: every balanced convex set $U\subseteq V$ such that $U\cap V_n$ is a neighbourhood of $0$ in $V_n$ for every $n$ is a neighbourhood of $0$ in $V$.
--
--   A strict colimit of Fréchet spaces is an **LF-space**; the prototypes are $C_c^\infty(\mathbb R^n)$ and the space $\mathbb C^\infty$ of eventually-zero sequences.
--
--   **Formalization Note** In the notes each $V_n$ has its own topology and $V_n$ carries the subspace topology of $V_{n+1}$. Here the $V_n$ get the subspace topology induced from $V$. By the theorem of Dieudonné–Schwartz the colimit topology induces the original topology on each step, so both descriptions give the same spaces. Convexity is real convexity, $V$ being a real vector space by restriction of scalars.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, pp. 2–3, §1.3 Strict colimits

import Mathlib

namespace GarrettFA

open Topology

/-- Garrett, *Completeness and quasi-completeness*, §1.3. The locally convex space `V` is the
strict (locally convex) colimit of the countable chain of subspaces `F 0 ⊂ F 1 ⊂ F 2 ⊂ ⋯`:
1. the containments are proper;
2. `V` is the union of the `F n`;
3. each `F n` is closed in `F (n+1)`;
4. `V` is locally convex (convexity is real convexity, `V` being a real vector space by
   restriction of scalars);
5. the topology of `V` is the locally convex colimit topology: every balanced convex
   subset `U ⊆ V` whose trace `U ∩ F n` is a neighbourhood of `0` in `F n` for every `n` is a
   neighbourhood of `0` in `V`.
Each `F n` carries the subspace topology induced from `V`. -/
structure IsStrictColimit (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] (F : ℕ → Submodule 𝕜 V) : Prop where
  strictMono : StrictMono F
  exists_mem : ∀ x : V, ∃ n, x ∈ F n
  isClosed_in_succ : ∀ n, IsClosed {y : F (n + 1) | (y : V) ∈ F n}
  locallyConvex : LocallyConvexSpace ℝ V
  mem_nhds_of_absConvex : ∀ U : Set V, Balanced 𝕜 U → Convex ℝ U →
    (∀ n, {y : F n | (y : V) ∈ U} ∈ 𝓝 (0 : F n)) → U ∈ 𝓝 (0 : V)

end GarrettFA


