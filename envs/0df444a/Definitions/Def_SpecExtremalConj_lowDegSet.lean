-- Prove2me | Definitions.Def_SpecExtremalConj_lowDegSet
-- name    : SpecExtremalConj_lowDegSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:20.274721+00:00
-- url     : https://prove2.me/theorems/86a08bbb-529d-4158-8b74-80b4c3b54fd2
-- title:
--   Low-degree set $L$, eq. (6)
-- statement:
--   Let $G$ be a graph on $n$ vertices, $r\ge 1$ and $\epsilon>0$. The **low-degree set** is
--
--   $$L=\Big\{v\in V(G) : d(v)\le\Big(1-\frac1r-3r\epsilon^{1/3}\Big)n\Big\},$$
--
--   where $d(v)$ is the degree of $v$.
--
--   Lemmas 3.4–3.6 show that $L$ is small and finally empty for a spectral extremal graph.
--
--   **Formalization Note** $\epsilon^{1/3}$ is the real power `ε ^ (1/3 : ℝ)`; every statement using $L$ assumes $\epsilon>0$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Lemma 3.4, p. 5, eq. (6)

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **The low-degree set L, eq. (6).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Lemma 3.4, p. 5, eq. (6):
"L := {v ∈ V(G) | d(v) ≤ (1 − 1/r − 3rǫ^{1/3}) n}."

`lowDegSet G r ε` is the set of vertices `v` of the graph `G` on `Fin n` with
`d(v) ≤ (1 − 1/r − 3 r ε^{1/3}) n`.

**Formalization Note.** `ε^{1/3}` is `Real.rpow ε (1/3)`; every statement using this set assumes
`ε > 0`. Decidability of the real inequality is classical. -/
noncomputable def lowDegSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (ε : ℝ) : Finset (Fin n) := by
  classical
  exact {v | (G.degree v : ℝ) ≤ (1 - 1 / (r : ℝ) - 3 * r * ε ^ ((1 : ℝ) / 3)) * n}

end SpecExtremalConj


