-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Geometry
-- name    : IsingVectorBalancing_Subgaussian_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:32:42.502576+00:00
-- url     : https://prove2.me/theorems/fe46ffab-ea96-4387-a796-51ee6d12c9ae
-- title:
--   Euclidean vectors and the no-three-parallel-unit condition
-- statement:
--   The input consists of a finite family $v_1,\ldots,v_n\in\mathbb R^d$ with its Euclidean inner product and norm. Two vectors are parallel unit vectors precisely when
--   $$\|u\|_2=\|v\|_2=1,\qquad u=v\ \text{or}\ u=-v.$$
--   An admissible family has $\|v_i\|_2\le1$ for every index and has no three distinct indices whose vectors are parallel unit vectors. Thus pairs of parallel unit inputs are permitted, as are arbitrary repetitions of shorter vectors. This is the geometric input condition for the explicit balancing law.
--
--   **Formalization Note** Vectors use `EuclideanSpace`; indices use `Fin n`. Empty families and zero dimensional Euclidean spaces are included.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 1 (PDF 2), §1, Eq. (1), Theorem 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Mathlib

set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Parallel unit vectors include antiparallel vectors. -/
def ParallelUnit {d : ℕ} (u v : Vec d) : Prop :=
  ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ (u = v ∨ u = -v)

/-- Exactly the unit-ball and no-three-distinct-parallel-unit assumptions. -/
def Admissible {n d : ℕ} (v : Fin n → Vec d) : Prop :=
  (∀ i, ‖v i‖ ≤ 1) ∧
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    ¬ (ParallelUnit (v i) (v j) ∧ ParallelUnit (v i) (v k))

end IsingVectorBalancing.Subgaussian


