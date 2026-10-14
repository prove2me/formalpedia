-- Prove2me | Definitions.Def_RobustAuction_ROM_Mechanism
-- name    : RobustAuction_ROM_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T19:32:45.963579+00:00
-- url     : https://prove2.me/theorems/c94a9a0a-4afc-4dd5-ae21-0e7cc30005d0
-- title:
--   Figures 1–2, pp. 1018–1019 — the robust optimal mechanism ROM: optimizers of (12)–(14), reservation prices (15), adapted allocations (16)–(19), allocation (20) and payments (21)
-- statement:
--   This module defines the robust optimal mechanism **ROM** of Bandi and Bertsimas, made of Algorithm ROM.a (Figure 1) and Algorithm ROM.b (Figure 2). The notation is that of the constraints of LP (5): $n$ buyers, $m$ items, an uncertainty set $\mathcal U$ of $n\times m$ valuation matrices, and budgets $B_i$.
--
--   **ROM.a** computes, before any bid is placed, the following quantities.
--
--   1. (12) The worst case valuation vector $\mathbf z\in\mathcal U$ and nominal allocation $\mathbf x^*$: $\mathbf x^*$ is optimal, at $\mathbf v=\mathbf z$, for the inner problem
--   $$\max_{x\ge 0}\ \sum_{i\in\mathcal N}\sum_{j\in\mathcal M}x_{ij}v_{ij}\quad\text{s.t.}\quad \sum_{i}x_{ij}\le 1\ \forall j,\quad \sum_{j}x_{ij}v_{ij}\le B_i\ \forall i,\quad \sum_{j}x_{ij}v_{ij}\le\sum_j x_{ij}u_{ij}\ \forall\mathbf u\in\mathcal U,\ \forall i,$$
--   and $\mathbf z$ maximizes the optimal value of this problem over $\mathbf v\in\mathcal U$.
--   2. (14) For each buyer $i$, a matrix $\tilde{\mathbf u}^i\in\mathcal U$ minimizing $\sum_{j}x^*_{ij}u_{ij}$ over $\mathbf u\in\mathcal U$. Write $\tilde u^i_j$ for its entry $(i,j)$.
--   3. (13) An optimal solution $(\xi^*,\eta^*,\theta^*)$ of
--   $$\min\ \sum_{j}\xi_j+\sum_{i}\Bigl(\eta_iB_i+\theta_i\sum_j x^*_{ij}\tilde u^i_j\Bigr)\quad\text{s.t.}\quad \xi_j+z_{ij}\eta_i+z_{ij}\theta_i\ge z_{ij}\ \forall i,j,\quad \xi_j,\eta_i,\theta_i\ge 0 .$$
--   4. (15) The reservation prices $r^*_{ij}=\xi^*_j+\eta^*_i z_{ij}+\theta^*_i z_{ij}$.
--
--   **ROM.b** runs on the bid vector $\mathbf v$. If $\mathbf v\notin\mathcal U$, nothing is allocated and nobody is charged. Otherwise let
--   $$\mathcal P=\Bigl\{\mathbf y\in\mathbb R^{n\times m}_+ \ \Bigm|\ \sum_{i}y_{ij}\le 1-\sum_i x^*_{ij}\ \forall j,\quad \sum_j y_{ij}u_{ij}\le B_i-\sum_j x^*_{ij}r^*_{ij}+\sum_j x^*_{ij}\theta^*_i\tilde u^i_j\ \forall\mathbf u\in\mathcal U,\ \forall i\Bigr\}\quad(18)$$
--   $$\mathcal Q_k=\Bigl\{\mathbf y\in\mathbb R^{n\times m}_+ \ \Bigm|\ \sum_{i\ne k}y_{ij}\le 1-\sum_{i}x^*_{ij}\ \forall j,\quad \sum_j y_{ij}u_{ij}\le B_i-\sum_j x^*_{ij}r^*_{ij}\ \forall\mathbf u\in\mathcal U,\ \forall i\ne k\Bigr\}\quad(19)$$
--   ROM.b then computes:
--
--   1. (16) an adapted allocation $\mathbf y^{\mathbf v}$ maximizing $\sum_{i}\sum_j y_{ij}(v_{ij}-r^*_{ij})$ over $\mathcal P$;
--   2. (17) for each buyer $k$, a matrix $\mathbf y^{\mathbf v-k}_{\cdot,k}$ maximizing $\sum_{i\ne k}\sum_j y_{ij}(v_{ij}-r^*_{ij})$ over $\mathcal Q_k$;
--   3. (20) the allocation $a^{\mathbf v}_{ij}=y^{\mathbf v}_{ij}+x^*_{ij}$;
--   4. (21) the payments
--   $$p^{\mathbf v}_k=\sum_j y^{\mathbf v}_{kj}r^*_{kj}+\sum_j x^*_{kj}r^*_{kj}-\sum_j x^*_{kj}\theta^*_k\tilde u^k_j+\sum_{i\ne k}\sum_j y^{\mathbf v-k}_{ij,k}(v_{ij}-r^*_{ij})-\sum_{i\ne k}\sum_j y^{\mathbf v}_{ij}(v_{ij}-r^*_{ij}).$$
--
--   The problems (12), (13), (14), (16), (17) need not have unique optimal solutions. The module therefore records one choice of all of them as data and defines two predicates. **IsROMa** says that the choice solves (12), (14) and (13). **IsROM** adds that it solves (16) and (17) at every bid vector in $\mathcal U$. A statement about ROM quantifies over every choice satisfying these predicates. The module also defines the allocation (20) and the payments (21) as functions of the bid vector.
--
--   The resulting mechanism resembles a VCG mechanism with item- and buyer-dependent reservation prices. The paper claims it is an optimal solution of (5); the mission states the part of that claim that holds, namely that ROM is feasible for (5).
--
--   **Formalization Note** The data structure `ROMData` holds $\mathbf z$, $\mathbf x^*$, $\xi^*,\eta^*,\theta^*$, the matrices $\tilde{\mathbf u}^i$ (as `ut i`, so that $\tilde u^i_j$ is `ut i i j`), and the selections $\mathbf v\mapsto\mathbf y^{\mathbf v}$ and $(k,\mathbf v)\mapsto\mathbf y^{\mathbf v-k}_{\cdot,k}$. The outer optimality in (12) is stated as: the objective of every inner-feasible $x$ at every $\mathbf v\in\mathcal U$ is at most $\sum x^*_{ij}z_{ij}$. In $\mathcal Q_k$, row $k$ is only required to be nonnegative; it enters neither the constraints nor the objective of (17). One printed slip is corrected: (18) writes $\sum_j x^*_{kj}\theta^*_i\tilde u^i_j$ with an index $k$ that is not bound in the definition of $\mathcal P$, and the module reads $x^*_{ij}$, which matches (13), (33) and (34). Allocation and payments are $0$ off $\mathcal U$ (step 1 of ROM.b).
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), pp. 1018–1019 (PDF pp. 8–9), Figure 1 (Algorithm ROM.a, Eqs. (12)–(15)) and Figure 2 (Algorithm ROM.b, Eqs. (16)–(21))

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP

namespace RobustAuction.ROM

open Finset Classical

/-!
The robust optimal mechanism ROM of Bandi and Bertsimas, Math. Oper. Res. 39(4) (2014), §2.3:
Algorithm ROM.a (Figure 1, p. 1018) and Algorithm ROM.b (Figure 2, p. 1019).

ROM is built from optimal solutions of the problems (12), (13), (14), (16) and (17), which need
not be unique. `ROMData` carries one choice of all of them; `IsROMa` and `IsROM` say that the
choice consists of optimal solutions of exactly those problems. Statements quantify over every
such choice.
-/

/-- One choice of the quantities computed by ROM:
* `z` — the worst case valuation vector of (12);
* `xs` — the nominal allocation `x*` of (12);
* `ξ`, `η`, `θ` — the optimal solution `(ξ*, η*, θ*)` of (13);
* `ut i` — the minimizing valuation matrix `ũ^i ∈ U` of (14) for buyer `i`
  (the paper's `ũ^i_j` is the entry `ut i i j`);
* `y v` — the adapted allocation `y^v` of (16) at bid vector `v`;
* `yk k v` — the temporary quantities `y^{v-k}_{·,k}` of (17) at bid vector `v`. -/
structure ROMData (n m : ℕ) where
  z : Fin n → Fin m → ℝ
  xs : Fin n → Fin m → ℝ
  ξ : Fin m → ℝ
  η : Fin n → ℝ
  θ : Fin n → ℝ
  ut : Fin n → Fin n → Fin m → ℝ
  y : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ
  yk : Fin n → (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ

/-- Feasibility of `x` for the inner problem of (12) at valuation vector `v`:
`x ≥ 0`, `∑_i x_ij ≤ 1` for all `j`, `∑_j x_ij v_ij ≤ B_i` for all `i`, and
`∑_j x_ij v_ij ≤ ∑_j x_ij u_ij` for all `u ∈ U` and all `i`. -/
def InnerFeasible {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (v x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ j, ∑ i, x i j ≤ 1) ∧ (∀ i, ∑ j, x i j * v i j ≤ B i) ∧
    ∀ u ∈ U, ∀ i, ∑ j, x i j * v i j ≤ ∑ j, x i j * u i j

/-- The objective `∑_i ∑_j x_ij v_ij` of the inner problem of (12). -/
def innerObj {n m : ℕ} (v x : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, x i j * v i j

/-- Feasibility for problem (13): `ξ_j, η_i, θ_i ≥ 0` and
`ξ_j + z_ij η_i + z_ij θ_i ≥ z_ij` for all `i`, `j`. -/
def DualFeasible {n m : ℕ} (z : Fin n → Fin m → ℝ) (ξ : Fin m → ℝ) (η θ : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ ξ j) ∧ (∀ i, 0 ≤ η i) ∧ (∀ i, 0 ≤ θ i) ∧
    ∀ i j, z i j ≤ ξ j + z i j * η i + z i j * θ i

/-- The objective of (13): `∑_j ξ_j + ∑_i (η_i B_i + θ_i ∑_j x*_ij ũ^i_j)`. -/
def dualObj {n m : ℕ} (B : Fin n → ℝ) (xs : Fin n → Fin m → ℝ) (ut : Fin n → Fin n → Fin m → ℝ)
    (ξ : Fin m → ℝ) (η θ : Fin n → ℝ) : ℝ :=
  ∑ j, ξ j + ∑ i, (η i * B i + θ i * ∑ j, xs i j * ut i i j)

/-- The reservation prices (15): `r*_ij = ξ*_j + η*_i z_ij + θ*_i z_ij`. -/
def rStar {n m : ℕ} (d : ROMData n m) (i : Fin n) (j : Fin m) : ℝ :=
  d.ξ j + d.η i * d.z i j + d.θ i * d.z i j

/-- The set `𝒫` of (18): `y ∈ ℝ₊^{n×m}` with `∑_i y_ij ≤ 1 - ∑_i x*_ij` for all `j`, and
`∑_j y_ij u_ij ≤ B_i - ∑_j x*_ij r*_ij + ∑_j x*_ij θ*_i ũ^i_j` for all `u ∈ U` and all `i`.
(The page prints `x*_kj` in the last sum, with an unbound `k`; the index is `i`.) -/
def PSet {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ) (d : ROMData n m) :
    Set (Fin n → Fin m → ℝ) :=
  {y | (∀ i j, 0 ≤ y i j) ∧ (∀ j, ∑ i, y i j ≤ 1 - ∑ i, d.xs i j) ∧
    ∀ u ∈ U, ∀ i, ∑ j, y i j * u i j ≤
      B i - ∑ j, d.xs i j * rStar d i j + ∑ j, d.xs i j * d.θ i * d.ut i i j}

/-- The set `𝒬_k` of (19): `y ∈ ℝ₊^{n×m}` with `∑_{i ≠ k} y_ij ≤ 1 - ∑_i x*_ij` for all `j`,
and `∑_j y_ij u_ij ≤ B_i - ∑_j x*_ij r*_ij` for all `u ∈ U` and all `i ≠ k`.
Row `k` is only required to be nonnegative; it does not enter the objective of (17). -/
def QSet {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ) (d : ROMData n m)
    (k : Fin n) : Set (Fin n → Fin m → ℝ) :=
  {y | (∀ i j, 0 ≤ y i j) ∧ (∀ j, ∑ i ∈ univ.erase k, y i j ≤ 1 - ∑ i, d.xs i j) ∧
    ∀ u ∈ U, ∀ i, i ≠ k → ∑ j, y i j * u i j ≤ B i - ∑ j, d.xs i j * rStar d i j}

/-- The objective of (16): `∑_i ∑_j y_ij (v_ij - r*_ij)`. -/
def welfare {n m : ℕ} (d : ROMData n m) (v y : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, y i j * (v i j - rStar d i j)

/-- The objective of (17): `∑_{i ≠ k} ∑_j y_ij (v_ij - r*_ij)`. -/
def welfareExcept {n m : ℕ} (d : ROMData n m) (k : Fin n) (v y : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i ∈ univ.erase k, ∑ j, y i j * (v i j - rStar d i j)

/-- Algorithm ROM.a (Figure 1): the data `d` consists of optimal solutions of (12), (14), (13).
1. (12): `z ∈ U`, `x*` is feasible for the inner problem at `z`, and the inner value at `z`
   attained by `x*` is at least the objective of every inner-feasible `x` at every `v ∈ U`.
2. (14): for each buyer `i`, `ũ^i ∈ U` minimizes `∑_j x*_ij u_ij` over `u ∈ U`.
3. (13): `(ξ*, η*, θ*)` is feasible for (13) and minimizes its objective. -/
def IsROMa {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ) (d : ROMData n m) : Prop :=
  d.z ∈ U ∧ InnerFeasible U B d.z d.xs ∧
    (∀ v ∈ U, ∀ x, InnerFeasible U B v x → innerObj v x ≤ innerObj d.z d.xs) ∧
    (∀ i, d.ut i ∈ U ∧ ∀ u ∈ U, ∑ j, d.xs i j * d.ut i i j ≤ ∑ j, d.xs i j * u i j) ∧
    DualFeasible d.z d.ξ d.η d.θ ∧
    ∀ (ξ : Fin m → ℝ) (η θ : Fin n → ℝ), DualFeasible d.z ξ η θ →
      dualObj B d.xs d.ut d.ξ d.η d.θ ≤ dualObj B d.xs d.ut ξ η θ

/-- ROM (Figures 1 and 2): `IsROMa`, and for every bid vector `v ∈ U`
* (16): `y^v ∈ 𝒫` maximizes `∑_i ∑_j y_ij (v_ij - r*_ij)` over `𝒫`;
* (17): for every buyer `k`, `y^{v-k}_{·,k} ∈ 𝒬_k` maximizes `∑_{i≠k} ∑_j y_ij (v_ij - r*_ij)`
  over `𝒬_k`. -/
def IsROM {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ) (d : ROMData n m) : Prop :=
  IsROMa U B d ∧ ∀ v ∈ U,
    (d.y v ∈ PSet U B d ∧ ∀ y ∈ PSet U B d, welfare d v y ≤ welfare d v (d.y v)) ∧
    ∀ k : Fin n, d.yk k v ∈ QSet U B d k ∧
      ∀ y ∈ QSet U B d k, welfareExcept d k v y ≤ welfareExcept d k v (d.yk k v)

/-- The allocation (20) of ROM.b: `a^v_ij = y^v_ij + x*_ij` if `v ∈ U`; nothing is allocated
if `v ∉ U` (step 1). -/
noncomputable def alloc {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (d : ROMData n m)
    (v : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  if v ∈ U then d.y v i j + d.xs i j else 0

/-- The payments (21) of ROM.b: if `v ∈ U`,
`p^v_k = ∑_j y^v_kj r*_kj + ∑_j x*_kj r*_kj - ∑_j x*_kj θ*_k ũ^k_j
  + ∑_{i≠k} ∑_j y^{v-k}_{ij,k} (v_ij - r*_ij) - ∑_{i≠k} ∑_j y^v_ij (v_ij - r*_ij)`;
the charge is zero if `v ∉ U` (step 1). -/
noncomputable def pay {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (d : ROMData n m)
    (v : Fin n → Fin m → ℝ) (k : Fin n) : ℝ :=
  if v ∈ U then
    ∑ j, d.y v k j * rStar d k j + ∑ j, d.xs k j * rStar d k j
      - ∑ j, d.xs k j * d.θ k * d.ut k k j
      + welfareExcept d k v (d.yk k v) - welfareExcept d k v (d.y v)
  else 0

end RobustAuction.ROM


