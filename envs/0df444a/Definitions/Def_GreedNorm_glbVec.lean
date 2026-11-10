-- Prove2me | Definitions.Def_GreedNorm_glbVec
-- name    : GreedNorm_glbVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:44.883067+00:00
-- url     : https://prove2.me/theorems/e9d48fe4-4bbf-445b-b344-1b9af3745187
-- title:
--   Processing-time vector $p_i[\sigma]$ of a machine
-- statement:
--   Let $J=\{1,\dots,n\}$ be a set of jobs, $M=\{1,\dots,m\}$ a set of machines, and $p_{ij}$ the processing time of job $j$ on machine $i$. For an assignment $\sigma:J\to M$ and a machine $i$, the vector $p_i[\sigma]\in\mathbb R^n$ has $j$-th coordinate
--
--   $$
--   p_i[\sigma]_j = p_{ij}\cdot \mathbf 1\{\sigma(j)=i\},
--   $$
--
--   that is, $p_{ij}$ for the jobs assigned to $i$ and $0$ for the others.
--
--   This is the argument of machine $i$'s norm in the Generalized Load Balancing problem.
--
--   **Formalization Note** Jobs are `Fin n`, machines `Fin m` (0-based); the processing times are a matrix `p : Fin m → Fin n → ℝ`.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3)

import Mathlib

namespace GreedNorm

/-- **The processing-time vector of machine `i` under an assignment** (`p_i[σ]`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3): "Under assignment σ : J → M, let pi[σ] := {pij · 1{σ(j)=i}}j∈J
denote the n-dimensional vector, where the j-th coordinate is equal to pij if σ(j) = i and zero
otherwise."

**Formalization Note** Jobs are `Fin n` and machines `Fin m` (0-based). Processing times are a
matrix `p : Fin m → Fin n → ℝ` (nonnegativity is a hypothesis of the theorems that use it). The
`j`-th coordinate is `p i j` when `σ j = i` and `0` otherwise. -/
def glbVec {n m : ℕ} (p : Fin m → Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) : Fin n → ℝ :=
  fun j => if σ j = i then p i j else 0

end GreedNorm


