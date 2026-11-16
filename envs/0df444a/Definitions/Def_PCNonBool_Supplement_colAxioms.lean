-- Prove2me | Definitions.Def_PCNonBool_Supplement_colAxioms
-- name    : PCNonBool_Supplement_colAxioms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:03.375399+00:00
-- url     : https://prove2.me/theorems/6c1fa17c-17f2-4bb7-8154-f3949bdb7211
-- title:
--   The colouring polynomials $\mathrm{Col}(G,k)$
-- statement:
--   Let $G=(V,E)$ be a simple graph and $k\ge1$. The set $\mathrm{Col}(G,k)$ [Bayer 1982], stating that $G$ is $k$-colourable with the $k$-th roots of unity as colours, has one variable $x_v$ per vertex and consists of
--
--   1. the range axioms $x_v^k-1$ for $v\in V$, saying that every vertex receives a $k$-th root of unity as colour;
--   2. the edge axioms
--   $$e(x_u,x_v)=\sum_{j=0}^{k-1}x_u^{\,j}x_v^{\,k-1-j}\qquad\text{for }(u,v)\in E,$$
--   which, over a field containing a primitive $k$-th root of unity, vanish on a pair of $k$-th roots of unity exactly when the two are different.
--
--   This is the polynomial system whose refutations Theorem 6.2 bounds from below.
--
--   **Formalization Note** $G$ is a Mathlib `SimpleGraph`; the edge axiom is symmetric in $u,v$, so taking it for both orientations of an edge adds nothing.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §6, (50a)–(50b), p.33 (PDF p.36)

import Mathlib

namespace PCNonBool.Supplement

open MvPolynomial

/-- The polynomial set `Col(G, k)` [Bayer 1982] stating that the graph `G = (V, E)` is
`k`-colourable with colours the `k`-th roots of unity (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §6, (50a)–(50b), p.33 (PDF p.36)):
one variable `x_v` per vertex, and

* the range axioms `x_v^k - 1` for `v ∈ V` (50a);
* the edge axioms `e(x_u, x_v) = ∑_{j=0}^{k-1} x_u^j x_v^{k-1-j}` for `(u, v) ∈ E` (50b).

**Formalization Note** `G` is a Mathlib `SimpleGraph` (simple, undirected, loopless, as on p.10).
The edge axiom is symmetric in `u, v`, so taking it for both orientations of an edge adds
nothing. -/
noncomputable def colAxioms {V F : Type*} [Field F] (G : SimpleGraph V) (k : ℕ) :
    Set (MvPolynomial V F) :=
  {p | (∃ v : V, p = X v ^ k - 1) ∨
    (∃ u v : V, G.Adj u v ∧ p = ∑ j ∈ Finset.range k, X u ^ j * X v ^ (k - 1 - j))}

end PCNonBool.Supplement


