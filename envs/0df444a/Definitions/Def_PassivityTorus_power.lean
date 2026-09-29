-- Prove2me | Definitions.Def_PassivityTorus_power
-- name    : PassivityTorus_power
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-24T04:19:41.873673+00:00
-- url     : https://prove2.me/theorems/091547a9-7e65-4134-9244-4ad3070fd36d
-- title:
--   Sites, one-step shift, and total power on a periodic $q$-dimensional lattice
-- statement:
--   Fix natural numbers $q$, $L$ and $d$. A **site** is a point $x \in (\mathbb{Z}/L\mathbb{Z})^q$ of the periodic cubic lattice with $q$ axes and $L$ sites along each. Moving $s$ steps along axis $a$ changes only coordinate $a$, to $x_a + s$ modulo $L$; write $x \pm e_a$ for one step forward or back.
--
--   Each link $(x, a)$ carries a real $d\times d$ matrix $W(x,a)$ and each site a velocity $v(x) \in \mathbb{R}^d$. The **total power** of the neighbour coupling is
--
--   $$
--   P_W(v) = \sum_{x} \sum_{a=0}^{q-1} v(x) \cdot \Bigl( W(x,a)\, v(x+e_a) - W(x-e_a,a)\, v(x-e_a) \Bigr),
--   $$
--
--   where the second term uses the matrix of the link behind $x$.
--
--   **Formalization Note** Sites are `Fin q → Fin L`; the step is `Function.update` on one coordinate with `Fin L` arithmetic, which wraps around. `[NeZero L]` is needed for the literal $1$ in `Fin L`.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (lattice of nodes; power of the coupling): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Matrix BigOperators

namespace PassivityTorus

/-- Sites of a periodic cubic lattice with q axes and L sites along each. -/
abbrev Site (q L : ℕ) := Fin q → Fin L

/-- Move s steps along axis a, wrapping around. -/
def shift {q L : ℕ} (x : Site q L) (a : Fin q) (s : Fin L) : Site q L :=
  Function.update x a (x a + s)

/-- Total power of the per-link neighbour coupling. -/
def power (q L d : ℕ) [NeZero L]
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ)
    (v : Site q L → (Fin d → ℝ)) : ℝ :=
  ∑ x : Site q L, ∑ a : Fin q,
    v x ⬝ᵥ (W x a *ᵥ v (shift x a 1) - W (shift x a (-1)) a *ᵥ v (shift x a (-1)))

end PassivityTorus


