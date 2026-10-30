-- Prove2me | Definitions.Def_SpecExtremalConj_heavySet
-- name    : SpecExtremalConj_heavySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:48.613577+00:00
-- url     : https://prove2.me/theorems/16997b9d-f968-4fb1-9fe3-c00573eac19a
-- title:
--   Set $W$ of vertices with many neighbours in their own part, eq. (5)
-- statement:
--   Let $G$ be a graph on $n$ vertices with a partition $V(G)=V_1\cup\dots\cup V_r$, and let $\theta>0$. The set
--
--   $$W=\bigcup_{i=1}^r\{v\in V_i : d_{V_i}(v)\ge 2\theta n\}$$
--
--   consists of the vertices having at least $2\theta n$ neighbours in their own part.
--
--   Lemma 3.4 shows $W\subseteq L$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Lemma 3.4, p. 5, eq. (5)

import Mathlib
import Definitions.Def_SpecExtremalConj_part
import Definitions.Def_SpecExtremalConj_degIn
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **The set W of vertices with many neighbours in their own part, eq. (5).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Lemma 3.4, p. 5,
eq. (5): "W := ∪_{i=1}^r {v ∈ V_i | d_{V_i}(v) ≥ 2θn}."

`heavySet G P θ` is the set of vertices `v` of the graph `G` on `Fin n` with
`d_{V_i}(v) ≥ 2θn`, where `V_i = part P (P v)` is the part containing `v`.

**Formalization Note.** `v ∈ V_i` exactly when `i = P v`, so the union over `i` is a single
condition on `v`. Decidability of the real inequality is classical. -/
noncomputable def heavySet {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Fin n → Fin r) (θ : ℝ) : Finset (Fin n) := by
  classical
  exact {v | 2 * θ * n ≤ (degIn G (part P (P v)) v : ℝ)}

end SpecExtremalConj


