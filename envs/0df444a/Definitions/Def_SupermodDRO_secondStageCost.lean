-- Prove2me | Definitions.Def_SupermodDRO_secondStageCost
-- name    : SupermodDRO_secondStageCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:53.930829+00:00
-- url     : https://prove2.me/theorems/328148c5-738e-4f9c-8161-468378b64b7e
-- title:
--   Second-stage cost $g(x,z)$ of Problem (1)
-- statement:
--   For a first-stage decision $x\in\mathbb R^l$ and a realization $z\in\mathbb R^n$ of the uncertainty, the **second-stage cost** is the optimal value of the linear program
--   $$
--   g(x,z)=\min_{y\in\mathbb R^m}\ \{\,b^\top y \;:\; Wx+Uy\ge Vz+v^0\,\},
--   $$
--   with data $b\in\mathbb R^m$, $W\in\mathbb R^{r\times l}$, $U\in\mathbb R^{r\times m}$, $V\in\mathbb R^{r\times n}$, $v^0\in\mathbb R^r$, and $g(x,z)=+\infty$ when the program is infeasible. The uncertainty enters only the right-hand side.
--
--   **Formalization Note** The value is the infimum in the extended reals $[-\infty,+\infty]$: an empty feasible set gives $+\infty$ (the paper's convention), an unbounded program gives $-\infty$. The inequality is componentwise.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, (1), p.6

import Mathlib

open Matrix

namespace SupermodDRO

/-- **The second-stage cost `g(x, z)`, Problem (1).** Long, Qi & Zhang, *Supermodularity in
Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022), §2.1, (1), p.6:
"g(x, z) = min b⊤y s.t. Wx + Uy ≥ Vz + v⁰, where b ∈ ℜᵐ, W ∈ ℜ^{r×l}, U ∈ ℜ^{r×m}, V ∈ ℜ^{r×n} and
v⁰ ∈ ℜʳ are given constants, and g(x, z) = ∞ if Problem (1) is infeasible."

**Formalization Note** The value is the infimum, in the extended reals `EReal`, of `b⊤y` over the
feasible `y ∈ ℝᵐ`. The infimum of the empty set is `⊤`, which is the paper's `g(x, z) = ∞` for an
infeasible problem; an unbounded-below problem gives `⊥`. The inequality `≥` is componentwise. -/
noncomputable def secondStageCost {l m r n : ℕ} (W : Matrix (Fin r) (Fin l) ℝ)
    (U : Matrix (Fin r) (Fin m) ℝ) (V : Matrix (Fin r) (Fin n) ℝ) (v0 : Fin r → ℝ)
    (b : Fin m → ℝ) (x : Fin l → ℝ) (z : Fin n → ℝ) : EReal :=
  ⨅ y ∈ {y : Fin m → ℝ | V *ᵥ z + v0 ≤ W *ᵥ x + U *ᵥ y}, ((b ⬝ᵥ y : ℝ) : EReal)

end SupermodDRO


