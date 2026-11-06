-- Prove2me | Definitions.Def_FlexibleNRM_vfa
-- name    : FlexibleNRM_vfa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:25:57.264036+00:00
-- url     : https://prove2.me/theorems/cf5a0c2a-8844-4829-9a4a-bc886d3ad38a
-- title:
--   The value function approximation $\hat J_t(x)$, Eq. (3)
-- statement:
--   The approximation to $J_t(x)$ is the optimal value of
--   $$\hat J_t(x)=\max_{(y,w)\in\mathbb Z_+}\Big\{\hat\Psi_t(w):\ \sum_{p\in\mathcal R_j}y_{jp}=x_j\ \ \forall j,\quad \sum_{j\in\mathcal J}\sum_{p\in\mathcal R_j}a_{ip}\,y_{jp}+w_i=c_i\ \ \forall i\Big\}.$$
--   It routes the purchases $x$ so as to maximize the resource-based approximation at the capacities that remain.
--
--   **Formalization Note** The maximum is the supremum of the attained values. These are finitely many, and they exist exactly when $\mathcal F(x)\ne\emptyset$. At an infeasible state the supremum is the junk value $0$, which is never used.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (3), p.9

import Mathlib
import Definitions.Def_FlexibleNRM_vfaResource

namespace FlexibleNRM

/-- The **value function approximation** `Ĵ_t(x)`, Eq. (3): the maximum of `Ψ̂_t(w)` over
`(y, w) ∈ Z₊` with `∑_{p ∈ R_j} y_jp = x_j` for all `j` and
`∑_j ∑_{p ∈ R_j} a_ip y_jp + w_i = c_i` for all `i`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (3), p.9.

**Formalization Note** The maximum is an `sSup` of the set of attained values. That set is finite
(`w` ranges over `0 ≤ w_i ≤ c_i`), and it is nonempty exactly when `F(x) ≠ ∅`, so for feasible `x`
the `sSup` is the paper's maximum. For infeasible `x`, where (3) has no feasible point, the `sSup`
is the junk value `0`. It is never used: in (7) it is multiplied by the indicator of `F(x + e_j) ≠ ∅`,
and Proposition 5.4 keeps the hypothesis `F(x) ≠ ∅`. -/
noncomputable def vfa {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ) (t : ℕ)
    (x : Fin n → ℕ) : ℝ :=
  sSup {v : ℝ | ∃ (y : Fin n → Fin r → ℕ) (w : Fin m → ℕ),
    (∀ j, ∑ p ∈ N.R j, y j p = x j) ∧
    (∀ i, ∑ j, ∑ p ∈ N.R j, N.a i p * y j p + w i = N.c i) ∧
    v = vfaResource N γ t (fun i => (w i : ℤ))}

end FlexibleNRM


