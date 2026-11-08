-- Prove2me | Definitions.Def_StreamColour_Certificate
-- name    : StreamColour_Certificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:51:59.738649+00:00
-- url     : https://prove2.me/theorems/8512fb45-59ba-4e89-a036-dde881c9738d
-- title:
--   Lemma 3.3 — the check from adjacency tests and retained edges
-- statement:
--   Given a test $T$ on pairs of vertices, a set $E'$ of edges, a set $R$ of vertices and an assignment $\varphi$ of colours, the **check** examines every pair of distinct vertices $u,v$ with $\varphi(u)=\varphi(v)$: if at least one endpoint lies in $R$ it requires that $T$ reports no edge, and otherwise it requires that $uv\notin E'$. It accepts when all these requirements hold.
--
--   **Formalization Note** The check takes only $T$, $E'$, $R$ and $\varphi$, so it has no access to a graph.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 3.3 and its proof, pp.22–23 (PDF 24–25)

import Mathlib

namespace StreamColour

/-! # The check of Lemma 3.3

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), Lemma 3.3 and its proof,
pp.22–23 (PDF 24–25): for every pair of distinct vertices receiving the same colour, test adjacency exactly if
at least one endpoint lies in `R`, and look the pair up among the retained edges otherwise.

**Formalization Note.** `check` takes only the tests, the retained edges, `R` and the assignment, so it has no
access to a graph. -/

/-- The check of Lemma 3.3, using only the adjacency tests `T` and the retained edges `E'`: for every pair of
distinct vertices with the same colour, the test (if the pair meets `R`) or the table (otherwise) must report no
edge. It has no access to a graph. -/
def check {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (T : V → V → Bool) (E' : Finset (Sym2 V))
    (R : Finset V) (φ : V → Fin q) : Bool :=
  decide (∀ u v, u ≠ v → φ u = φ v →
    if u ∈ R ∨ v ∈ R then T u v = false else s(u, v) ∉ E')

end StreamColour


