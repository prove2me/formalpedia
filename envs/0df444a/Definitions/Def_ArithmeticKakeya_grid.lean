-- Prove2me | Definitions.Def_ArithmeticKakeya_grid
-- name    : ArithmeticKakeya_grid
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T21:54:27.809525+00:00
-- url     : https://prove2.me/theorems/b0b3cd43-ed82-4983-9dd2-ccfe33acda5e
-- title:
--   Constructible graphs for arithmetic Kakeya
-- statement:
--   The combinatorial substrate of the arithmetic Kakeya problem. `grid d` enumerates the vertices $[e_1,\dots,e_k]$ with $1\le e_i\le d_i$. A `ConstructibleGraph` over a dilate set $X\subset\mathbb Z^2$ consists of dimensions $d_1,\dots,d_k$ and stage labellings $f_i$ on the prefix grid $d_1\times\cdots\times(d_i-1)$, where a non-zero label lies in $X$ (a zero label means no edge). The vertex count is $n(G)=d_1\cdots d_k$ and the edge count $m(G)=\sum_i(\#\text{non-zero }f_i)\,d_{i+1}\cdots d_k$. `edgeFn` is the $\mathbb Z^2$-valued function contributed by one labelled edge, sending its two endpoints to $\pm\mathbf{x}$ and all other vertices to $0$. These are the definitions of the source's Verifiable Set-up.
-- source:
--   https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya (Verifiable Set-up / Introduction)

import Mathlib

namespace ArithmeticKakeya

open Finset

/-- `grid d` enumerates the vertices of `d_1 × ⋯ × d_k`: all lists `[e_1,…,e_k]`
with `1 ≤ e_i ≤ d_i`, each exactly once. -/
def grid : List ℕ → List (List ℕ)
  | [] => [[]]
  | d :: ds => (List.range' 1 d).foldr (fun a acc => (grid ds).map (fun t => a :: t) ++ acc) []

/-- The prefix domain of stage `i` (0-indexed): `d.take i ++ [d[i] − 1]`. -/
def domainDims (d : List ℕ) (i : Fin d.length) : List ℕ :=
  d.take i.val ++ [d.get i - 1]

/-- An `X`-constructible graph. A non-zero label `f i e` is allowed only on the prefix
domain `domainDims dims i` and must then lie in `X`; a zero value means "no edge". -/
structure ConstructibleGraph (X : Finset (ℤ × ℤ)) where
  dims : List ℕ
  f : (i : Fin dims.length) → List ℕ → ℤ × ℤ
  f_support : ∀ (i : Fin dims.length) (e : List ℕ),
    f i e ≠ (0, 0) → e ∈ grid (domainDims dims i) ∧ f i e ∈ X

/-- The number of vertices `n(G) = d_1 ⋯ d_k`. -/
def n {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) : ℕ := G.dims.prod

/-- The number of edges `m(G) = Σ_i (# non-zero entries of f_i) · d_{i+1} ⋯ d_k`. -/
def m {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) : ℕ :=
  Finset.sum Finset.univ (fun i : Fin G.dims.length =>
    ((grid (domainDims G.dims i)).filter (fun e => decide (G.f i e ≠ (0, 0)))).length *
      (G.dims.drop (i.val + 1)).prod)

/-- The edge function for stage `i`, prefix `a`, suffix `c`: sends `a ++ c` to `f i a`,
`(a with last coordinate +1) ++ c` to its negation, and all other vertices to `(0,0)`. -/
def edgeFn {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X)
    (i : Fin G.dims.length) (a c : List ℕ) : List ℕ → ℤ × ℤ :=
  let x := G.f i a
  let e₁ := a ++ c
  let e₂ := a.dropLast ++ [a.getLastD 0 + 1] ++ c
  fun g => if g = e₁ then x else if g = e₂ then -x else (0, 0)

end ArithmeticKakeya


