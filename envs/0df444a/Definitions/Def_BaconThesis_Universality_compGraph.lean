-- Prove2me | Definitions.Def_BaconThesis_Universality_compGraph
-- name    : BaconThesis_Universality_compGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:15.179985+00:00
-- url     : https://prove2.me/theorems/20d2fb42-f3ac-4953-940c-c4956a0d04da
-- title:
--   The graph of computationally connected subsystems
-- statement:
--   For a gate set $G$ on $n$ subsystems $\mathcal H=\bigotimes_{i}\mathbb C^{d_i}$, the **graph of computationally connected subsystems** is the simple graph with vertex set $\{0,\dots,n-1\}$ (the subsystems) in which $a$ and $b$ are adjacent exactly when $a\ne b$ and the two subsystems are computationally connected for $G$.
--
--   Lemma 4.3.2 asserts that connectedness of this graph suffices for $G$ to densely generate the special unitary group of the whole space.
--
--   **Formalization Note** Built with `SimpleGraph.fromRel`, which symmetrizes the relation; computational connectedness is symmetric in substance (swap the two tensor factors of $V$), so no edge changes.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Lemma 4.3.2, p.52 (PDF p.69)

import Mathlib
import Definitions.Def_BaconThesis_Universality_CompConnected

namespace BaconThesis.Universality

/-- **The graph of computationally connected subsystems.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§4.3.1, Lemma 4.3.2, p.52 (PDF p.69): "Let G be the graph of computationally connected subsystems
for a given gate set."

The simple graph on the `n` subsystems in which `a` and `b` are adjacent when `a ≠ b` and they are
computationally connected (`CompConnected`), in either order.

**Formalization Note.** `SimpleGraph.fromRel` symmetrizes the relation; computational
connectedness is symmetric in `a, b` in substance (swap the two tensor factors of `V`), so the
symmetrization changes no edge. Vertices are `Fin n` (subsystems `0, …, n-1`). -/
def compGraph {n : ℕ} (d : Fin n → ℕ)
    (G : Set (Matrix.unitaryGroup ((i : Fin n) → Fin (d i)) ℂ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (CompConnected d G)

end BaconThesis.Universality


