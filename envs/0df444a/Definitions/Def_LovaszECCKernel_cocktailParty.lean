-- Prove2me | Definitions.Def_LovaszECCKernel_cocktailParty
-- name    : LovaszECCKernel_cocktailParty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:05.307079+00:00
-- url     : https://prove2.me/theorems/125e62f5-8fb4-4f47-9208-853f0ff60308
-- title:
--   Cocktail-party graphs with universal vertices
-- statement:
--   The **cocktail-party graph** on $2n$ vertices is the complement of a perfect matching: vertices $(i,b)$ with $i\in\{0,\dots,n-1\}$, $b\in\{0,1\}$, and $(i,b)\sim(j,c)$ iff $i\ne j$. Adding $u\ge 0$ **universal vertices** (adjacent to every other vertex) gives the graph $\mathrm{CP}(n,u)$ on $2n+u$ vertices.
--
--   These graphs appear between two cliques of a deletion sequence of a complete multipartite graph; covering them with few cliques is what Lemmas 5–8 exploit.
--
--   **Formalization Note** Vertex type $(\mathrm{Fin}\,n\times\mathrm{Bool})\oplus\mathrm{Fin}\,u$; every cocktail-party graph with $u$ universal vertices is isomorphic to it.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §3.3.2 and Proposition 7, p.34 (= PDF p.34)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- The **cocktail-party graph on `2n` vertices with `u` universal vertices added** (Fomin,
Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of
the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…),
§3.3.2, p.34 (= PDF p.34)): "Graphs that are complements of perfect matchings are widely known as
cocktail-party graphs", and Proposition 7: "a cocktail-party graph with 2n vertices … with an
arbitrary number of universal vertices added above".

**Formalization Note** Vertex set `(Fin n × Bool) ⊕ Fin u`. The `2n` cocktail-party vertices are
`(i, b)`; `(i, b)` and `(j, c)` are adjacent iff `i ≠ j`, so the non-edges are exactly the perfect
matching `{(i, false), (i, true)}`. The `u` added vertices are universal: adjacent to every other
vertex. Every cocktail-party graph with `u` universal vertices is isomorphic to this one. -/
def cocktailParty (n u : ℕ) : SimpleGraph ((Fin n × Bool) ⊕ Fin u) where
  Adj x y := x ≠ y ∧ match x, y with
    | .inl a, .inl b => a.1 ≠ b.1
    | _, _ => True
  symm := ⟨fun x y h => ⟨h.1.symm, by
    rcases x with a | a <;> rcases y with b | b <;> simp_all [eq_comm]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end LovaszECCKernel


