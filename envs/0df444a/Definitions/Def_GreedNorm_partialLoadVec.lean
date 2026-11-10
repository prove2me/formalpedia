-- Prove2me | Definitions.Def_GreedNorm_partialLoadVec
-- name    : GreedNorm_partialLoadVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:49.974314+00:00
-- url     : https://prove2.me/theorems/64ef030d-4bd8-4a39-98b9-322ed952bab9
-- title:
--   Load vector of a (partial) assignment
-- statement:
--   Given load functions $\mathrm{load}_i:2^U\to\mathbb R$ and a partial assignment $\tau$ of the elements of $U$ to $[m]$, the load vector is
--
--   $$
--   \mathrm{load}(\tau)=\bigl(\mathrm{load}_i(\tau^{-1}(i))\bigr)_{i\in[m]}.
--   $$
--
--   The cost of $\tau$ in Nested Cost Allocation is $g(\mathrm{load}(\tau))$.
--
--   **Formalization Note** A partial assignment is `τ : U → Option (Fin m)` (`none` = unassigned); a total assignment $\sigma$ is `fun e => some (σ e)`.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.2, p.2 (PDF 4)

import Mathlib

namespace GreedNorm

/-- **The load vector of a (partial) assignment** in Nested Cost Allocation:
`load(σ) = (load_i(σ^{-1}(i)))_{i ∈ [m]}`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.2, p.2 (PDF 4): "For an assignment σ, define cov(σ) to be the set of elements
that get assigned to one of the m parts, and the load vector to be load(σ) ∈ R^m whose i-th entry is
loadi(σ−1(i))."

**Formalization Note** A partial assignment is `τ : U → Option (Fin m)` (`none` = unassigned);
a total assignment `σ : U → Fin m` is `fun e => some (σ e)`. Entry `i` is `load i` of
`{e | τ e = some i}`. -/
def partialLoadVec {m : ℕ} {U : Type} [Fintype U] (load : Fin m → Finset U → ℝ)
    (τ : U → Option (Fin m)) : Fin m → ℝ :=
  fun i => load i (Finset.univ.filter (fun e => τ e = some i))

end GreedNorm


