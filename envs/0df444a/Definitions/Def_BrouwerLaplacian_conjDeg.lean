-- Prove2me | Definitions.Def_BrouwerLaplacian_conjDeg
-- name    : BrouwerLaplacian_conjDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:08.548196+00:00
-- url     : https://prove2.me/theorems/e4a214ea-d338-47ae-ad15-b3e796d577f7
-- title:
--   Conjugate degree sequence $d'_k$
-- statement:
--   Let $G$ be a finite simple graph. For $k\in\mathbb N$, the **conjugate degree** $d'_k$ is the number of vertices of $G$ whose degree is at least $k$:
--
--   $$d'_k=\#\{v : \deg_G(v)\ge k\}.$$
--
--   The sequence $(d'_1,d'_2,\dots,d'_n)$ is the **conjugate degree sequence** of $G$. It is the comparison sequence of the Grone–Merris–Bai theorem, which bounds partial sums of the Laplacian spectrum by partial sums of $d'$.
--
--   **Formalization Note** The value is a natural number defined for every $k$; the paper uses $1\le k\le n$.
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Definition 1.1, p.1

import Mathlib

namespace BrouwerLaplacian

open Finset

/-- **Conjugate degree sequence** `d′ₖ` of a graph.
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Definition 1.1, p.1:
"For a graph G, let d′ₖ be the number of vertices in G of degree at least k. Then,
(d′₁, d′₂, · · · , d′ₙ) is called the conjugate degree sequence of G."

`conjDeg G k` is the number of vertices `v` with `k ≤ deg v`.

**Formalization Note.** The value is a natural number, defined for every `k : ℕ` (the paper
uses `1 ≤ k ≤ n`); at `k = 0` it is the number of vertices. -/
def conjDeg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  #{v | k ≤ G.degree v}

end BrouwerLaplacian


