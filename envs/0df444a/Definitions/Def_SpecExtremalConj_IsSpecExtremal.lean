-- Prove2me | Definitions.Def_SpecExtremalConj_IsSpecExtremal
-- name    : SpecExtremalConj_IsSpecExtremal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:23.336699+00:00
-- url     : https://prove2.me/theorems/c2bc0c25-dd74-42d1-8d14-ce35d74cecd1
-- title:
--   Spectral extremal graph: $G \in \mathrm{Ex}_{sp}(n,F)$
-- statement:
--   Let $F$ be a graph. A graph $G$ on $n$ vertices is **$F$-free** if no subgraph of $G$ (not necessarily induced) is isomorphic to $F$. The graph $G$ is a **spectral extremal graph** for $F$, written $G\in\mathrm{Ex}_{sp}(n,F)$, if $G$ is $F$-free and
--
--   $$\lambda(G')\le\lambda(G)\qquad\text{for every }F\text{-free graph }G'\text{ on the same }n\text{ vertices}.$$
--
--   Theorem 1.2 states that spectral extremal graphs are extremal (maximum number of edges) for large $n$.
--
--   **Formalization Note** Graphs on $n$ vertices are graphs on `Fin n`; $F$-freeness is Mathlib's `F.Free G` ($F$ is not contained in $G$ as a subgraph). The comparison is with every $F$-free graph on `Fin n`, not only with members of $\mathrm{Ex}(n,F)$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §1, p. 1 (definition of Ex_sp(n, F)) and Theorem 1.2, p. 2

import Mathlib
import Definitions.Def_SpecExtremalConj_specRad
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Spectral extremal graph, G ∈ Ex_sp(n, F).** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §1, p. 1 (unnumbered): "The graph which
attains the maximum spectral radius is called a spectral extremal graph. We denote by Ex_sp(n, F)
the set of all spectral extremal graphs for F"; Theorem 1.2, p. 2: "G has the maximal spectral
radius over all n-vertex F-free graphs".

`IsSpecExtremal F G` says that `G` is `F`-free (no subgraph isomorphic to `F`, not necessarily
induced: Mathlib's `F.Free G`) and `specRad G' ≤ specRad G` for every `F`-free graph `G'` on
the same vertex set `Fin n`.

**Formalization Note.** "n-vertex graphs" are graphs on `Fin n`; the comparison is with every
`F`-free graph on `Fin n` (not only with members of Ex(n, F)). Freeness and λ are invariant under
relabelling, so this is the paper's notion. -/
def IsSpecExtremal {W : Type*} (F : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Prop :=
  F.Free G ∧ ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj], F.Free G' → specRad G' ≤ specRad G

end SpecExtremalConj


