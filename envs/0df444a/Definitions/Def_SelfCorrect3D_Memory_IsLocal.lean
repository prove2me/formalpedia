-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_IsLocal
-- name    : SelfCorrect3D_Memory_IsLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:11.947863+00:00
-- url     : https://prove2.me/theorems/2630a0e3-85dd-44c5-be9b-6f92723ccff8
-- title:
--   Hamiltonian terms local in $\mathbb R^3$ with radius $r$
-- statement:
--   Given positions $\mathrm{pos}:\{1,\dots,n\}\to\mathbb R^3$ of the qubits of a CSS code, the code is **local with radius $r$** if for every row of $H_x$ and every row of $H_z$ there is a point $c\in\mathbb R^3$ such that all qubits in the support of that row lie in the closed ball of radius $r$ around $c$. This is condition 1 of Theorem 1.2: "The support of each Hamiltonian term is contained in a ball of radius $O(1)$."
--
--   **Formalization Note** A Hamiltonian term is the term $(1-S)/2$ of one row. Positions need not be distinct.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Theorem 1.2 (1), p. 4

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode

namespace SelfCorrect3D.Memory

/-- **Locality of the Hamiltonian terms in ℝ³ with radius `r`.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
Theorem 1.2 (1), p. 4: "(Local) The support of each Hamiltonian term is contained in a ball of
radius O(1)". For qubit positions `pos : Fin n → ℝ³`: the support of every row of `H_x` and of
`H_z` lies in some closed ball of radius `r`.

**Formalization Note.** A Hamiltonian term is one row of `H_x` or `H_z` (the term
`(1 − S)/2`, supported on the row's support). Positions need not be injective. -/
def IsLocal {n mX mZ : ℕ} (C : CSSCode n mX mZ) (pos : Fin n → EuclideanSpace ℝ (Fin 3))
    (r : ℝ) : Prop :=
  (∀ a, ∃ c : EuclideanSpace ℝ (Fin 3), ∀ q, C.HX a q ≠ 0 → dist (pos q) c ≤ r) ∧
    ∀ b, ∃ c : EuclideanSpace ℝ (Fin 3), ∀ q, C.HZ b q ≠ 0 → dist (pos q) c ≤ r

end SelfCorrect3D.Memory


