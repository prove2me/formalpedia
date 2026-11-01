-- Prove2me | Definitions.Def_AssignToSeatRM_StaticLP
-- name    : AssignToSeatRM_StaticLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:00.349612+00:00
-- url     : https://prove2.me/theorems/577f2f47-58d8-46d5-966e-0deeeeb49d04
-- title:
--   The static problems: the IP (1), its LP relaxation (2) and the aggregated LP (3)
-- statement:
--   Let $C\in\{0,1\}^{N\times M}$ be a capacity matrix, $p_{ij}$ the prices and $d_{ij}$ the demands of the itineraries $i\to j$.
--
--   **IP (1) and LP (2).** With $x_{k,ij}$ the amount of requests $i\to j$ served by seat $k$,
--
--   $$\max\ \sum_{1\le i\le j\le M}p_{ij}\sum_{k=1}^Nx_{k,ij}\quad\text{s.t.}\quad\sum_{k=1}^N x_{k,ij}\le d_{ij},\qquad \sum_{(i,j):\,i\le\ell\le j}x_{k,ij}\le C_{k\ell}\ \ (k\in[N],\ \ell\in[M]),$$
--
--   with $x_{k,ij}\in\{0,1\}$ in (1) and $x_{k,ij}\ge0$ in the relaxation (2).
--
--   **Aggregated LP (3).** With $c_\ell=\sum_{k=1}^NC_{k\ell}$ the number of seats free on leg $\ell$ and $x_{ij}$ the number of accepted requests $i\to j$,
--
--   $$\max\ \sum_{1\le i\le j\le M}p_{ij}x_{ij}\quad\text{s.t.}\quad 0\le x_{ij}\le d_{ij},\qquad\sum_{(i,j):\,i\le\ell\le j}x_{ij}\le c_\ell\ \ (\ell\in[M]).$$
--
--   The module defines the feasible sets and the optimal values `ip1Value`, `lp2Value`, `lp3Value`. The value of LP (2) on the realized demand is the hindsight optimum of the dynamic problem; (3) drops the assign-to-seat restriction.
--
--   **Formalization Note** Each optimal value is the supremum of the objective over the feasible set; for $d\ge0$ this set contains $x=0$ and is bounded, so the supremum is the maximum. The IP takes integer demands $d:\mathbb N\times\mathbb N\to\mathbb N$.
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, (1) p.9, (2) pp.9–10, (3) p.11

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-! # The static problems: the IP (1), its LP relaxation (2) and the aggregated LP (3)

Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023, doi:10.1287/msom.2023.1188, (1) and (2)
(pp.9–10), (3) (p.11).

**Formalization Note.**
1. A seat-level allocation is `x : Fin N → ℕ × ℕ → ℝ`, `x k (i, j) = x_{k,ij}`; only the
   itineraries in `itins M` are variables (the other values enter neither the objective nor the
   constraints). An aggregated allocation is `x : ℕ × ℕ → ℝ`.
2. Demands and prices are `d p : ℕ → ℕ → ℝ`, read at `(i, j) ∈ itins M`.
3. Each optimal value is the `sSup` of the objective over the feasible set. For `d ≥ 0` the
   feasible set contains `x = 0` and is bounded (every `x_{k,ij} ∈ [0, 1]`, every
   `x_{ij} ∈ [0, d_{ij}]`), so the `sSup` is the maximum of the LP. -/

/-- The constraints of LP (2) (pp.9–10) for capacity matrix `C` and demand `d`:
`x_{k,ij} ≥ 0`; `Σ_k x_{k,ij} ≤ d_{ij}` for every `i ≤ j`;
`Σ_{(i,j): i ≤ ℓ ≤ j} x_{k,ij} ≤ C_{kℓ}` for every seat `k` and leg `ℓ ∈ [M]`. -/
def IsFeasLP2 {N M : ℕ} (C : CapMat N M) (d : ℕ → ℕ → ℝ) (x : Fin N → ℕ × ℕ → ℝ) : Prop :=
  (∀ k, ∀ ij ∈ itins M, 0 ≤ x k ij) ∧
  (∀ ij ∈ itins M, ∑ k, x k ij ≤ d ij.1 ij.2) ∧
  (∀ k, ∀ ℓ ∈ Finset.Icc 1 M,
    ∑ ij ∈ (itins M).filter (fun ij => ij.1 ≤ ℓ ∧ ℓ ≤ ij.2), x k ij ≤ capR C k ℓ)

/-- The constraints of the IP (1) (p.9): those of (2) and `x_{k,ij} ∈ {0, 1}`. -/
def IsFeasIP1 {N M : ℕ} (C : CapMat N M) (d : ℕ → ℕ → ℝ) (x : Fin N → ℕ × ℕ → ℝ) : Prop :=
  IsFeasLP2 C d x ∧ ∀ k, ∀ ij ∈ itins M, x k ij = 0 ∨ x k ij = 1

/-- The objective of (1) and (2): `Σ_{i ≤ j} p_{ij} Σ_k x_{k,ij}`. -/
def seatRevenue {N : ℕ} (M : ℕ) (p : ℕ → ℕ → ℝ) (x : Fin N → ℕ × ℕ → ℝ) : ℝ :=
  ∑ ij ∈ itins M, p ij.1 ij.2 * ∑ k, x k ij

/-- The optimal value of the IP (1) (p.9) for nonnegative integer demands `d`. -/
def ip1Value {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℕ) : ℝ :=
  sSup (seatRevenue M p '' {x | IsFeasIP1 C (fun i j => (d i j : ℝ)) x})

/-- The optimal value of the LP relaxation (2) (pp.9–10). -/
def lp2Value {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝ) : ℝ :=
  sSup (seatRevenue M p '' {x | IsFeasLP2 C d x})

/-- The aggregated capacity `c_ℓ = Σ_{k=1}^N C_{kℓ}` (p.11). -/
def aggCap {N M : ℕ} (C : CapMat N M) (ℓ : ℕ) : ℝ :=
  ∑ k, capR C k ℓ

/-- The constraints of the aggregated LP (3) (p.11): `0 ≤ x_{ij} ≤ d_{ij}` for every `i ≤ j`
and `Σ_{(i,j): i ≤ ℓ ≤ j} x_{ij} ≤ c_ℓ` for every leg `ℓ ∈ [M]`. -/
def IsFeasLP3 {N M : ℕ} (C : CapMat N M) (d : ℕ → ℕ → ℝ) (x : ℕ × ℕ → ℝ) : Prop :=
  (∀ ij ∈ itins M, 0 ≤ x ij ∧ x ij ≤ d ij.1 ij.2) ∧
  (∀ ℓ ∈ Finset.Icc 1 M,
    ∑ ij ∈ (itins M).filter (fun ij => ij.1 ≤ ℓ ∧ ℓ ≤ ij.2), x ij ≤ aggCap C ℓ)

/-- The optimal value of the aggregated LP (3) (p.11): maximize `Σ_{i ≤ j} p_{ij} x_{ij}`. -/
def lp3Value {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝ) : ℝ :=
  sSup ((fun x : ℕ × ℕ → ℝ => ∑ ij ∈ itins M, p ij.1 ij.2 * x ij) '' {x | IsFeasLP3 C d x})

end AssignToSeatRM


