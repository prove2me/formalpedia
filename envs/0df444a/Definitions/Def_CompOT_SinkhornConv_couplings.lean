-- Prove2me | Definitions.Def_CompOT_SinkhornConv_couplings
-- name    : CompOT_SinkhornConv_couplings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:19:46.240128+00:00
-- url     : https://prove2.me/theorems/5fc704f1-8d2a-4adf-affa-2b3d39855487
-- title:
--   Couplings $U(a,b)$ (transportation polytope)
-- statement:
--   For $a\in\mathbb R^n$ and $b\in\mathbb R^m$, the set of **couplings** is
--   $$U(a,b) = \{P\in\mathbb R_+^{n\times m} : P\mathbb 1_m = a,\ P^\top\mathbb 1_n = b\},$$
--   the nonnegative matrices whose row sums are $a$ and whose column sums are $b$.
--
--   For histograms $a\in\Sigma_n$, $b\in\Sigma_m$ this is the feasible set of Kantorovich's optimal transport problem and of its entropic regularization (4.2); it always contains the product coupling $ab^\top$.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §2.3, eq. (2.10), p. 370

import Mathlib

open Matrix

namespace CompOT.SinkhornConv

/-- **The transportation polytope `U(a, b)` of couplings.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §2.3, eq. (2.10), p. 370: "U(a, b) := {P ∈ Rn×m+ : P1m = a and PT1n = b}".

`couplings a b` is the set of `n × m` real matrices `P` with nonnegative entries whose row sums
are `a` (`P 1_m = a`) and whose column sums are `b` (`Pᵀ 1_n = b`).

**Formalization Note.** `P *ᵥ 1` is the vector of row sums and `Pᵀ *ᵥ 1` the vector of column
sums; `1` is the all-ones vector. -/
def couplings {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) : Set (Matrix (Fin n) (Fin m) ℝ) :=
  {P | (∀ i j, 0 ≤ P i j) ∧ P *ᵥ 1 = a ∧ Pᵀ *ᵥ 1 = b}

end CompOT.SinkhornConv


