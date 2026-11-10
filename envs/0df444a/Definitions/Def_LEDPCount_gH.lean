-- Prove2me | Definitions.Def_LEDPCount_gH
-- name    : LEDPCount_gH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:32.927987+00:00
-- url     : https://prove2.me/theorems/6b1e09e8-d98f-4f59-862c-c429c73b4a83
-- title:
--   The edge-set count $g_H(n,c)$ from the proof of Lemma 3.2
-- statement:
--   For a pattern $H$ with $\ell$ edges, let $E(K_n)$ be the set of unordered pairs of distinct vertices of $[n]$, and for $C\subseteq E(K_n)$ let $V(C)$ be the set of vertices incident to $C$. For $c\ge0$,
--   $$
--   g_H(n,c)=\sum_{\substack{C\subseteq E(K_n)\\ 2\le|C|\le\ell,\ |V(C)|=c}}\#\bigl\{(\phi,\phi'):\phi,\phi':V(H)\hookrightarrow[n],\ C\subseteq\phi(E(H))\cap\phi'(E(H))\bigr\}.
--   $$
--   It is the combinatorial quantity to which the proof of Lemma 3.2 reduces the variance of the main term of LNC.
--
--   **Formalization Note** `gIndex` is the outer index set, `gPairs C` the inner set of pairs of injections, `vertexSet C` is $V(C)$.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Lemma 3.2, p.20 (PDF p.22); §2.1 notation V(E′), p.14

import Mathlib

namespace LEDPCount

/-- `V(C)`, the set of vertices incident to the edges of an edge set `C` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…,
§2.1, p.14, PDF p.16). -/
def vertexSet {n : ℕ} (C : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ e ∈ C, v ∈ e

/-- The index set of `g_H(n, c)` in the proof of Lemma 3.2 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.20, PDF p.22):
the edge sets `C ⊆ E(K_n)` with `2 ≤ |C| ≤ ℓ` and `|V(C)| = c`, where `ℓ = |E(H)|`.
`E(K_n)` is the set of non-diagonal unordered pairs. -/
def gIndex {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (n c : ℕ) :
    Finset (Finset (Sym2 (Fin n))) :=
  Finset.univ.filter fun C => (∀ e ∈ C, ¬ e.IsDiag) ∧ 2 ≤ C.card ∧
    C.card ≤ H.edgeFinset.card ∧ (vertexSet C).card = c

/-- The inner index set of `g_H(n, c)` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.20, PDF p.22): the pairs of
injections `ϕ, ϕ' : V(H) ↪ [n]` with `C ⊆ ϕ(E(H)) ∩ ϕ'(E(H))`. -/
noncomputable def gPairs {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] {n : ℕ}
    (C : Finset (Sym2 (Fin n))) : Finset ((Fin k ↪ Fin n) × (Fin k ↪ Fin n)) :=
  Finset.univ.filter fun p => C ⊆ H.edgeFinset.image (Sym2.map p.1) ∧
    C ⊆ H.edgeFinset.image (Sym2.map p.2)

/-- `g_H(n, c)` from the proof of Lemma 3.2 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.20, PDF p.22):
`g_H(n, c) = ∑_{C ⊆ E(K_n), 2 ≤ |C| ≤ ℓ, |V(C)| = c} #{(ϕ, ϕ') : C ⊆ ϕ(E(H)) ∩ ϕ'(E(H))}`. -/
noncomputable def gH {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (n c : ℕ) : ℕ :=
  ∑ C ∈ gIndex H n c, (gPairs H C).card

end LEDPCount


