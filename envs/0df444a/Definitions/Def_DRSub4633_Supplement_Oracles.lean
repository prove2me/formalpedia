-- Prove2me | Definitions.Def_DRSub4633_Supplement_Oracles
-- name    : DRSub4633_Supplement_Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:26:01.564932+00:00
-- url     : https://prove2.me/theorems/0d9986b3-b646-42ea-a990-55f39685447d
-- title:
--   The oracle answer maps
-- statement:
--   An oracle bundle consists of four maps on $\mathbb R^n$: a value map $y\mapsto f(y)$, a gradient map $y\mapsto\nabla f(y)$, an LMO selection $c\mapsto z(c)\in\arg\max_{z\in K}\langle c,z\rangle$, and a projection selection $v\mapsto\Pi_{K_W}(v)$. Which maps are admissible for a given objective and feasible set is stated in Theorem 6.3.
--
--   The oracles are deterministic: the paper fixes the tie-breaking of the LMO once and for all, and requires it to be Borel measurable.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, pp.7–8

import Mathlib

namespace DRSub4633.Supplement

/-- **The oracle answers available to an algorithm.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, pp.7–8.

An `Oracles n` bundles four answer maps: `val` (objective values), `grad` (objective gradients),
`lmo` (the linear maximization oracle's selection `c ↦ z`) and `proj` (the projection oracle's
selection `v ↦ z`). Which maps are admissible for an objective `f` and a feasible set `K` is
stated in each theorem (`val = f`, `grad = ∇f` within the cube, `lmo` a Borel measurable
maximizer selection, `proj` the Euclidean projection onto `K_W`).

**Formalization Note.** The oracles are deterministic: "tie-breaking is fixed and Borel
measurable" (p.7). -/
structure Oracles (n : ℕ) where
  val : EuclideanSpace ℝ (Fin n) → ℝ
  grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  lmo : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  proj : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)

end DRSub4633.Supplement


