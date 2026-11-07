-- Prove2me | Definitions.Def_DynSort_cross
-- name    : DynSort_cross
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:09.806922+00:00
-- url     : https://prove2.me/theorems/9860b97c-4b3b-4884-9178-cbecb53b7486
-- title:
--   Threshold crossings $\mathrm{cross}_z(S)$
-- statement:
--   For a threshold $z\in\mathbb R$ and a sequence $S=(x_1,\dots,x_k)$ of reals, $\mathrm{cross}_z(S)$ is the number of adjacent pairs with one element at most $z$ and the other greater than $z$:
--   $$\mathrm{cross}_z(S)=\bigl|\{\,j\in[k-1] : (x_j>z)\neq(x_{j+1}>z)\,\}\bigr| .$$
--   It is $0$ for a sequence with at most one element.
--
--   Integrating the crossing count over all thresholds recovers the cost (equation (1)), so bounds on crossings at every threshold give competitive-ratio bounds.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §2, p.6 (PDF p.8)

import Mathlib

namespace DynSort

/-! # Threshold crossings

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, p.6 (PDF p.8).

For a threshold `z ∈ ℝ`, `cross_z(S) = |{j ∈ [k − 1] : (x_j > z) ≠ (x_{j+1} > z)}|`: the number of
adjacent pairs with one element at most `z` and the other greater than `z`; zero for at most one
element.

**Formalization Note.** The adjacent pairs are `S.zip S.tail`, so `cross z [] = cross z [x] = 0`.
-/

/-- **Threshold crossings** (§2, p.6): the number of adjacent pairs `(x_j, x_{j+1})` of `S` with
`(x_j > z) ≠ (x_{j+1} > z)`. -/
noncomputable def cross (z : ℝ) (S : List ℝ) : ℕ :=
  ((S.zip S.tail).filter (fun p => decide ((z < p.1) ≠ (z < p.2)))).length

end DynSort


