-- Prove2me | Definitions.Def_SubexpPrimes_Net
-- name    : SubexpPrimes_Net
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:29.299667+00:00
-- url     : https://prove2.me/theorems/4b8ca9f7-65fe-40da-9982-a62d2c012e86
-- title:
--   Network $G$ and its contraction $Z(G)$
-- statement:
--   A **network** is a finite loopless multigraph $G=(V,E)$ in which every edge carries one bit and every vertex $v$ has an entry function $T_v:\{0,1\}^{E(v)}\to R$ on the bits of its incident edges $E(v)$. Its **contraction** is
--
--   $$
--   Z(G)=\sum_{x\in\{0,1\}^E}\ \prod_{v\in V} T_v\big(x|_{E(v)}\big),
--   $$
--
--   its size is $m=|E|$ and its degree is $\max_v|E(v)|$. The contraction **with the input fixed** to a word $d$ sums only over the assignments $x$ whose designated input edges carry $d$.
--
--   Every algorithm of the paper writes the quantity it wants as a short combination of such contractions.
--
--   **Formalization Note** Parallel edges are distinct bits. An edge always has two endpoints, so an edge that is free on one side ends in a unary vertex. The entries lie in a commutative semiring: $\mathbb Q$ in Definition 2.1, and the truncated polynomial ring in Lemma A.23.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Definition 2.1, p.13; Lemma 5.1, p.22

import Mathlib

set_option autoImplicit false

namespace SubexpPrimes

/-- **Network** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), Definition 2.1, p.13.

A finite loopless multigraph: `ends e` is the pair of endpoints of the edge `e`, and `loopless`
says they differ. Every edge carries one bit, and every vertex `v` has an entry function
`table v` reading the bits on its own edges `E(v) = {e | v is an endpoint of e}`.

**Formalization Note.** `V` and `E` are arbitrary types; parallel edges are distinct elements of
`E`, hence distinct bits. An edge always has two endpoints, so an edge that is free on one side
ends in a unary vertex (p.14). A table is a function on the subtype of incident edges, so no
order on `E(v)` is needed here; the machine encoding uses the increasing edge order. Entries lie
in `R`: the paper's `ℚ` for Definition 2.1, and `R_{P,ℓ}` for Lemma A.23. -/
structure Net (V E R : Type*) where
  /-- the two endpoints of each edge -/
  ends : E → V × V
  /-- no loops -/
  loopless : ∀ e, (ends e).1 ≠ (ends e).2
  /-- the entry function of a vertex, reading the bits of its incident edges -/
  table : (v : V) → ({e : E // (ends e).1 = v ∨ (ends e).2 = v} → Bool) → R

namespace Net

variable {V E R : Type*}

/-- The degree `|E(v)|` of `v`: incident edges, parallel edges counted with multiplicity. -/
def deg [Fintype E] [DecidableEq V] (G : Net V E R) (v : V) : ℕ :=
  (Finset.univ.filter fun e => (G.ends e).1 = v ∨ (G.ends e).2 = v).card

/-- The degree `max_v |E(v)|` of `G` (`0` when `G` has no vertex). -/
def maxDeg [Fintype V] [Fintype E] [DecidableEq V] (G : Net V E R) : ℕ :=
  Finset.univ.sup G.deg

/-- **The contraction** (Definition 2.1, p.13): `Z(G) = ∑_{x ∈ {0,1}^E} ∏_v T_v(x|_{E(v)})`. -/
def Z [Fintype V] [Fintype E] [DecidableEq E] [CommSemiring R] (G : Net V E R) : R :=
  ∑ x : E → Bool, ∏ v, G.table v (fun e => x e.1)

/-- **The contraction with the input fixed** (Lemma 5.1, p.22): the sum over the assignments `x`
whose designated input edges `inputs` carry the word `d`. -/
def ZFixed [Fintype V] [Fintype E] [DecidableEq E] [CommSemiring R] (G : Net V E R)
    (inputs : List E) (d : List Bool) : R :=
  ∑ x : E → Bool with inputs.map x = d, ∏ v, G.table v (fun e => x e.1)

end Net

end SubexpPrimes


