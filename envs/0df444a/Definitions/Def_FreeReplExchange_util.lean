-- Prove2me | Definitions.Def_FreeReplExchange_util
-- name    : FreeReplExchange_util
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:47.565634+00:00
-- url     : https://prove2.me/theorems/3798a3f4-7b1f-4ee6-bff7-3b07fe9d9a37
-- title:
--   Utilities (3), sign conditions, ESC and condition (19)
-- statement:
--   There is a finite set $A$ of agents and a set $[m]$ of goods. An **allocation** $x\in\{0,1\}^{A\times[m]}$ records which agent–good **slots** $(j,r)$ are filled. Agent $i$ has a utility matrix $U_i\in\mathbb R^{A\times[m]}$, and the **sign conditions** require
--   $$(U_i)_{i,r}\in(0,1],\qquad (U_i)_{j,r}\in[-1,0)\quad (j\neq i).$$
--   Her utility at $x$ is
--   $$\tilde u_i(x)=\langle U_i,x\rangle=\sum_{j\in A}\sum_{r=1}^m (U_i)_{j,r}\,x_{j,r}.$$
--   An instance satisfies **ESC** (equal valuation with symmetric competition) if there are factors $\beta_{ij}=\beta_{ji}\in(0,1)$ for distinct $i,j$ with $(U_i)_{i,r}=1$ and $(U_i)_{j,r}=-\beta_{ij}$ for every good $r$ and every $j\neq i$. **Condition (19)** requires
--   $$(U_i)_{i,s}+(U_i)_{j,r}\ge 0\qquad\text{for every } i\neq j \text{ and every } r,s\in[m].$$
--   The module also defines the number of filled slots $\sum_{i,r}x_{i,r}$ and the coordinatewise order $x\ge x'$ of allocations.
--
--   These are the standing objects of every statement of the mission: utilities, the hypotheses of the IR and NIC guarantees, and the count maximized by efficiency.
--
--   **Formalization Note** Agents form a finite type, goods are `Fin m`, an allocation is a function `A → Fin m → Bool`, and `U i j r` is $(U_i)_{j,r}$. The ESC factor $\beta$ is a function on all pairs; its diagonal is not used.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), §2.1, p.13 (PDF p.15), eq. (3), ESC; §4.3, p.33 (PDF p.35), eq. (19); eq. (12), p.18

import Mathlib

namespace FreeReplExchange

/-- The sign conditions on utility matrices of Yang–Kandasamy, *Pairwise Exchanges of Freely
Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…),
§2.1, p.13 (PDF p.15): `(U_i)_{i,r} ∈ (0, 1]` and `(U_i)_{j,r} ∈ [−1, 0)` for `j ≠ i`.

**Formalization Note.** Agents form a finite type `A`, goods are `Fin m`, and `U i j r` is the
entry `(U_i)_{j,r}`: the contribution of agent `j` possessing good `r` to agent `i`'s utility. -/
def SignCond {A : Type*} {m : ℕ} (U : A → A → Fin m → ℝ) : Prop :=
  (∀ i r, 0 < U i i r ∧ U i i r ≤ 1) ∧ (∀ i j r, j ≠ i → -1 ≤ U i j r ∧ U i j r < 0)

/-- Agent `i`'s utility (3), p.13, at an allocation `x`: `ũ_i(x) = Σ_j Σ_r (U_i)_{j,r} x_{j,r}`.

**Formalization Note.** An allocation `x ∈ {0,1}^{n×m}` is a function `A → Fin m → Bool`;
`x j r = true` means that slot `(j, r)` is filled. -/
noncomputable def util {A : Type*} [Fintype A] {m : ℕ} (U : A → A → Fin m → ℝ) (i : A)
    (x : A → Fin m → Bool) : ℝ :=
  ∑ j, ∑ r, if x j r then U i j r else 0

/-- The ESC condition (equal valuation with symmetric competition), p.13: there are symmetric
factors `β_ij = β_ji ∈ (0, 1)` for distinct `i, j` with `(U_i)_{i,r} = 1` and
`(U_i)_{j,r} = −β_ij` for every good `r` and every `j ≠ i`.

**Formalization Note.** `β` is a function on all pairs; its diagonal values are not used. -/
def IsESC {A : Type*} {m : ℕ} (U : A → A → Fin m → ℝ) (β : A → A → ℝ) : Prop :=
  (∀ i j, i ≠ j → β i j = β j i) ∧ (∀ i j, i ≠ j → 0 < β i j ∧ β i j < 1) ∧
  (∀ i r, U i i r = 1) ∧ (∀ i j r, j ≠ i → U i j r = -β i j)

/-- Condition (19), p.33 (PDF p.35): `(U_i)_{i,s} + (U_i)_{j,r} ≥ 0` for every `i ≠ j` and every
goods `r, s`. -/
def Cond19 {A : Type*} {m : ℕ} (U : A → A → Fin m → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ r s : Fin m, 0 ≤ U i i s + U i j r

/-- The number of filled slots `Σ_{i∈A} Σ_{r=1}^m x_{i,r}` of an allocation (the quantity in the
efficiency criterion (12), p.18). -/
def filledCount {A : Type*} [Fintype A] {m : ℕ} (x : A → Fin m → Bool) : ℕ :=
  ∑ i, ∑ r, if x i r then 1 else 0

/-- `x ≥ x'` coordinatewise for allocations (p.13: "all allocations satisfy `x ≥ x^(0)`"). -/
def Dominates {A : Type*} {m : ℕ} (x' x : A → Fin m → Bool) : Prop :=
  ∀ i r, x' i r = true → x i r = true

end FreeReplExchange


