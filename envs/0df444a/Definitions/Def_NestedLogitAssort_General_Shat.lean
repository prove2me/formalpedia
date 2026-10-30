-- Prove2me | Definitions.Def_NestedLogitAssort_General_Shat
-- name    : NestedLogitAssort_General_Shat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:31.66816+00:00
-- url     : https://prove2.me/theorems/77669c29-08a0-43d0-9c28-a73772cc4061
-- title:
--   Greedy assortment $\hat S_i(\epsilon_i)$
-- statement:
--   The continuous knapsack (11) is solved by sorting the products by revenue and filling the capacity $\epsilon$, starting from the product with the largest revenue and considering only the products with $v_{ij}\le\epsilon$; $\hat z_i(\epsilon)$ is the resulting solution and
--
--   $$
--   \hat S_i(\epsilon)=\{j\in N:\ \hat z_{ij}(\epsilon)=1\}
--   $$
--
--   is the set of products that fit entirely. Here $\hat S_i(\epsilon)$ is the set of products $j$ with $v_{ij}\le\epsilon$ and $\mathrm{pre}_{ij}(\epsilon)+v_{ij}\le\epsilon$.
--
--   **Formalization Note** The fill runs in index order (revenue order, ties by index) and stops at the first eligible product that does not fit entirely: a later product of weight $0$ is not included. Such products change neither $\sum r_{ij}v_{ij}$ nor $V_i$, so constraint values are the same as under the convention that includes them, and with this convention $\hat S_i(\epsilon)$ is always one of the assortments $N^k_{ij}$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 5, pp. 23–24

import Mathlib
import Definitions.Def_NestedLogitAssort_General_pre

namespace NestedLogitAssort.General

/-- **The assortment `Ŝ_i(ϵ_i) = {j ∈ N : ẑ_{ij}(ϵ_i) = 1}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 5, pp. 23–24 (unnumbered): `ẑ_i(ϵ_i)` is the solution of the continuous knapsack
(11) "by sorting the products with respect to their revenues and filling the knapsack starting from
the product with the largest revenue, as long as we only consider the products whose preference
weights do not exceed `ϵ_i`", and `Ŝ_i(ϵ_i) = {j ∈ N : ẑ_{ij}(ϵ_i) = 1}`.

`Shat I i ε` is the set of eligible products (`v_{ij} ≤ ϵ`) that fit entirely once the eligible
products before them are filled.

**Formalization Note.** The fill proceeds in index order (revenue order, ties by index) and stops
at the first eligible product that does not fit entirely: a later product of weight `0` is not
taken. Such products change neither `∑ r_{ij} v_{ij}` nor `V_i`, so the constraint values of (3) are
the same under either convention. -/
noncomputable def Shat {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => I.v i j ≤ ε ∧ pre I i ε j + I.v i j ≤ ε)

end NestedLogitAssort.General


