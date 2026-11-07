-- Prove2me | Definitions.Def_UncrowdedColoring_fOne
-- name    : UncrowdedColoring_fOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:37.011122+00:00
-- url     : https://prove2.me/theorems/bfedd5ce-2834-42e6-88c5-77f49ca7c797
-- title:
--   The initial restriction hypergraphs $F_{1,c}$
-- statement:
--   Given a hypergraph $H$ and trimmed lists $L_1$, $F_{1,c}$ is the hypergraph on $V(H)$ with edge set $\{e\in E(H):c\in\bigcap_{v\in e}L_1(v)\}$.
--
--   This is the starting family of the iteration, the subject of Proposition 4.6.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), p.18

import Mathlib

open scoped Classical

namespace UncrowdedColoring

/-- The edges of `F_{1,c}` (p.18): "the hypergraph with vertex set V(H) and edge set
{e ∈ E(H) : c ∈ ⋂_{v∈e} L_1(v)}." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.18.)

**Formalization Note.** `U` is `V(H)` as a `Finset`; every edge of `H` is a subset of `V(H)`, so the
filter over `U.powerset` selects exactly the edges of `H` with the stated property. -/
noncomputable def fOne {V : Type*} (H : Hypergraph V) (U : Finset V) (L₁ : V → Finset ℕ) (c : ℕ) :
    Finset (Finset V) :=
  U.powerset.filter fun e => (e : Set V) ∈ H.edgeSet ∧ ∀ v ∈ e, c ∈ L₁ v

end UncrowdedColoring


