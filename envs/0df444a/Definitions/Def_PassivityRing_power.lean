-- Prove2me | Definitions.Def_PassivityRing_power
-- name    : PassivityRing_power
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-23T21:54:11.011226+00:00
-- url     : https://prove2.me/theorems/12ae7792-8a24-4d98-923a-45c4a5305cd1
-- title:
--   Total power of the per-link neighbour coupling on a ring of $N$ sites
-- statement:
--   Let $N \ge 1$ and $d$ be natural numbers. A ring has $N$ sites indexed by $\mathbb{Z}/N\mathbb{Z}$, so $i+1$ and $i-1$ are taken modulo $N$. Each site carries a velocity $v_i \in \mathbb{R}^d$, and each link carries a real $d\times d$ matrix $W_i$. The force on site $i$ is $W_i v_{i+1} - W_{i-1} v_{i-1}$, and the **total power** of the coupling is
--
--   $$
--   P_W(v) = \sum_{i \in \mathbb{Z}/N\mathbb{Z}} v_i \cdot \bigl( W_i\, v_{i+1} - W_{i-1}\, v_{i-1} \bigr),
--   $$
--
--   where $\cdot$ is the dot product on $\mathbb{R}^d$. Note that the second term uses the previous link's matrix $W_{i-1}$.
--
--   This is the quantity whose identical vanishing ("passivity") the mission characterizes.
--
--   **Formalization Note** Sites are `Fin N`, whose addition and subtraction wrap around modulo $N$; `[NeZero N]` is needed for the literal $1$ in `Fin N`.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (power of the coupling): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Matrix BigOperators

namespace PassivityRing

/-- Total power of the per-link neighbour coupling on a ring of N sites. -/
def power (N d : ℕ) [NeZero N] (W : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (v : Fin N → (Fin d → ℝ)) : ℝ :=
  ∑ i : Fin N, v i ⬝ᵥ (W i *ᵥ v (i + 1) - W (i - 1) *ᵥ v (i - 1))

end PassivityRing


