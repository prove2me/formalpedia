-- Prove2me | Definitions.Def_GyoriLovasz_IsTermMatching
-- name    : GyoriLovasz_IsTermMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:24.366226+00:00
-- url     : https://prove2.me/theorems/bc2ba61e-cec2-4586-a68f-9901961a7e1e
-- title:
--   Matching from pre-terminals to terminals; secondary edges
-- statement:
--   A **matching from pre-terminals to terminals** assigns to each terminal $t_i$ a non-terminal $p_i$ with $(p_i,t_i)\in E$, the $p_i$ pairwise distinct (Lemma 4.8). A family of **secondary edges** (Algorithm 3, line 2) chooses for each $p_i$ an edge $e_i=(p_i,q_i)\in E$ distinct from $(p_i,t_i)$.
--
--   **Formalization Note** The matching and the secondary edges are indexed by the terminal itself: $p(t)$ and $\mathrm{sec}(t)$ for $t\in T$; values off $T$ are never read.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Lemma 4.8, p.29; Algorithm 3, p.25; §4.1, p.24

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **Matching from pre-terminals to terminals.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Lemma 4.8, p.29: "there exist distinct vertices
p_1, ..., p_k ∈ PT(G, T) such that (p_i, t_i) ∈ E for all i ∈ [k]."

**Formalization Note.** `p` is indexed by the terminal itself and read on `T` only. -/
def IsTermMatching {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (p : V → V) : Prop :=
  (∀ t ∈ T, p t ∈ G.verts \ T ∧ (p t, t) ∈ G.arcs) ∧ Set.InjOn p T

/-- **Secondary edges.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Algorithm 3, line 2, p.25, and §4.1, p.24: for each `p_i`, an outgoing edge
`e_i = (p_i, q_i)` other than the matching edge `(p_i, t_i)`. -/
def IsSecondary {V : Type*} (G : DG V) (T : Finset V) (p : V → V) (sec : V → V × V) : Prop :=
  ∀ t ∈ T, sec t ∈ G.arcs ∧ (sec t).1 = p t ∧ (sec t).2 ≠ t

end GyoriLovasz


