-- Prove2me | Definitions.Def_AssignToSeatRM_BidPriceLP
-- name    : AssignToSeatRM_BidPriceLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:05.463295+00:00
-- url     : https://prove2.me/theorems/61cea4f2-791e-4658-8618-5839f941ccc8
-- title:
--   The bid-price LPs (6) and (12) and the bid-prices (13)
-- statement:
--   Let $C$ be a capacity matrix, $p_{ij}$ the prices and $\lambda_{ij}\ge0$ the expected demands.
--
--   **LP (6)** (the dual of (2) with $d=\lambda$): minimize $\sum_{i\le j}\lambda_{ij}z_{ij}+\sum_{k=1}^N\sum_{\ell=1}^MC_{k\ell}\beta_{k\ell}$ subject to
--
--   $$z_{ij}+\sum_{\ell=i}^{j}\beta_{k\ell}\ \ge\ p_{ij}\quad(1\le i\le j\le M,\ k\in[N]),\qquad z_{ij}\ge0,\quad\beta_{k\ell}\ge0.$$
--
--   **LP (12)** (bid-prices of maximal sequences, with coefficients $A_{uv}$): minimize $\sum_{i\le j}\lambda_{ij}z^\dagger_{ij}+\sum_{u\le v}A_{uv}\beta^\dagger_{uv}$ subject to
--
--   $$z^\dagger_{ij}+\beta^\dagger_{uv}\ \ge\ p_{ij}+\beta^\dagger_{u(i-1)}+\beta^\dagger_{(j+1)v}\quad(u\le i\le j\le v),\qquad z^\dagger_{ij}\ge0,\ \beta^\dagger_{ij}\ge0\ (i\le j),\qquad \beta^\dagger_{ij}=0\ (i>j).$$
--
--   Optimal solutions of both minimization problems are defined directly (feasible, with objective at most that of every feasible point). For $N\ge1$ and seat bid-prices $\beta$, the bid-prices (13) are $\beta^\dagger_{uv}=\min_{k\in[N]}\sum_{\ell=u}^{v}\beta_{k\ell}$ for $u\le v$ and $0$ for $u>v$.
--
--   These LPs give the two bid-price policies of the paper (BPC-S and BPC-M); Theorem 3 compares them.
--
--   **Formalization Note** $z$ is a function on pairs, $\beta$ a function of a seat and a 1-based leg, $\beta^\dagger$ a function on pairs of naturals; the constraint $\beta^\dagger_{ij}=0$ is imposed for all $i>j$ (only $\beta^\dagger_{u(u-1)}$ and $\beta^\dagger_{(v+1)v}$ occur).
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, (6) p.15, (12) and (13) p.17

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-! # The bid-price LPs (6) and (12)

Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023, doi:10.1287/msom.2023.1188, (6) (p.15)
and (12) (p.17).

**Formalization Note.**
1. `lam : ℕ → ℕ → ℝ` is the vector of expected demands `λ_{ij}` in the objectives (in the paper
   `λ_{ij} = λ^{[t,T]}_{ij}`). `z : ℕ × ℕ → ℝ`, `z (i, j) = z_{ij}`.
2. In (6) the seat bid-prices are `β : Fin N → ℕ → ℝ`, `β k ℓ = β_{kℓ}` for the 1-based leg `ℓ`.
3. In (12) the maximal-sequence bid-prices are `β† : ℕ → ℕ → ℝ`, `β† u v = β†_{uv}`; the
   constraint `β†_{ij} = 0` for `i > j` is imposed for all natural `i > j` (only
   `β†_{u(u−1)}` and `β†_{(v+1)v}` occur). `A : ℕ → ℕ → ℝ` holds the coefficients `A_{uv}`.
4. "Optimal solution" is stated directly: feasible, with objective at most that of every
   feasible point (both are minimization problems). -/

/-- The constraints of (6) (p.15): `z_{ij} + Σ_{ℓ=i}^{j} β_{kℓ} ≥ p_{ij}` for every `i ≤ j`
and seat `k`; `z_{ij} ≥ 0`; `β_{kℓ} ≥ 0` for `k ∈ [N]`, `ℓ ∈ [M]`. -/
def IsFeasLP6 {N : ℕ} (M : ℕ) (p : ℕ → ℕ → ℝ) (z : ℕ × ℕ → ℝ) (β : Fin N → ℕ → ℝ) :
    Prop :=
  (∀ ij ∈ itins M, ∀ k, p ij.1 ij.2 ≤ z ij + ∑ ℓ ∈ Finset.Icc ij.1 ij.2, β k ℓ) ∧
  (∀ ij ∈ itins M, 0 ≤ z ij) ∧
  (∀ k, ∀ ℓ ∈ Finset.Icc 1 M, 0 ≤ β k ℓ)

/-- The objective of (6): `Σ_{i ≤ j} λ_{ij} z_{ij} + Σ_k Σ_{ℓ=1}^{M} C_{kℓ} β_{kℓ}`. -/
def obj6 {N M : ℕ} (C : CapMat N M) (lam : ℕ → ℕ → ℝ) (z : ℕ × ℕ → ℝ) (β : Fin N → ℕ → ℝ) :
    ℝ :=
  ∑ ij ∈ itins M, lam ij.1 ij.2 * z ij + ∑ k, ∑ ℓ ∈ Finset.Icc 1 M, capR C k ℓ * β k ℓ

/-- `(z, β)` is an optimal solution of (6) (p.15) for capacity matrix `C`, prices `p` and
expected demands `lam` (minimization). -/
def IsOptLP6 {N M : ℕ} (C : CapMat N M) (p lam : ℕ → ℕ → ℝ) (z : ℕ × ℕ → ℝ)
    (β : Fin N → ℕ → ℝ) : Prop :=
  IsFeasLP6 M p z β ∧
    ∀ (z' : ℕ × ℕ → ℝ) (β' : Fin N → ℕ → ℝ), IsFeasLP6 M p z' β' →
      obj6 C lam z β ≤ obj6 C lam z' β'

/-- The constraints of (12) (p.17):
`z†_{ij} + β†_{uv} ≥ p_{ij} + β†_{u(i−1)} + β†_{(j+1)v}` for every `u ≤ i ≤ j ≤ v`;
`z†_{ij} ≥ 0`, `β†_{ij} ≥ 0` for `i ≤ j`; `β†_{ij} = 0` for `i > j`. -/
def IsFeasLP12 (M : ℕ) (p : ℕ → ℕ → ℝ) (z : ℕ × ℕ → ℝ) (βd : ℕ → ℕ → ℝ) : Prop :=
  (∀ ij ∈ itins M, ∀ uv ∈ envs M ij.1 ij.2,
    p ij.1 ij.2 + βd uv.1 (ij.1 - 1) + βd (ij.2 + 1) uv.2 ≤ z ij + βd uv.1 uv.2) ∧
  (∀ ij ∈ itins M, 0 ≤ z ij ∧ 0 ≤ βd ij.1 ij.2) ∧
  (∀ i j : ℕ, j < i → βd i j = 0)

/-- The objective of (12): `Σ_{i ≤ j} λ_{ij} z†_{ij} + Σ_{u ≤ v} A_{uv} β†_{uv}`. -/
def obj12 (M : ℕ) (A lam : ℕ → ℕ → ℝ) (z : ℕ × ℕ → ℝ) (βd : ℕ → ℕ → ℝ) : ℝ :=
  ∑ ij ∈ itins M, lam ij.1 ij.2 * z ij + ∑ uv ∈ itins M, A uv.1 uv.2 * βd uv.1 uv.2

/-- `(z†, β†)` is an optimal solution of (12) (p.17) with coefficients `A`, prices `p` and
expected demands `lam` (minimization). -/
def IsOptLP12 (M : ℕ) (p A lam : ℕ → ℕ → ℝ) (z : ℕ × ℕ → ℝ) (βd : ℕ → ℕ → ℝ) : Prop :=
  IsFeasLP12 M p z βd ∧
    ∀ (z' : ℕ × ℕ → ℝ) (βd' : ℕ → ℕ → ℝ), IsFeasLP12 M p z' βd' →
      obj12 M A lam z βd ≤ obj12 M A lam z' βd'

/-- The bid-prices (13) (p.17) built from seat bid-prices `β`:
`β†_{uv} = min_{k ∈ [N]} Σ_{ℓ: u ≤ ℓ ≤ v} β_{kℓ}` for `u ≤ v`, and `β†_{uv} = 0` for `u > v`
(the convention of (12)). The minimum needs `N ≥ 1`. -/
def minSeatBidPrice {N : ℕ} (hN : 0 < N) (β : Fin N → ℕ → ℝ) (u v : ℕ) : ℝ :=
  if u ≤ v then
    (Finset.univ : Finset (Fin N)).inf' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (fun k => ∑ ℓ ∈ Finset.Icc u v, β k ℓ)
  else 0

end AssignToSeatRM


