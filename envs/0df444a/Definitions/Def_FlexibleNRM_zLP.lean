-- Prove2me | Definitions.Def_FlexibleNRM_zLP
-- name    : FlexibleNRM_zLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:36.51723+00:00
-- url     : https://prove2.me/theorems/09b71852-685e-4c98-8c4c-36c112bd8122
-- title:
--   Linear program (8) and its value $Z^*_{\mathrm{LP}}$
-- statement:
--   With decision variables $h_t(S)$, the probability of offering $S$ at period $t$, and $y_{jp}$, the expected number of purchases of $j$ assigned to route $p$, consider
--   $$Z^*_{\mathrm{LP}}=\max\ \sum_{t\in\mathcal T}\sum_{S\subseteq\mathcal J}\sum_{j\in\mathcal J}f_j\,\phi_{jt}(S)\,h_t(S)$$
--   subject to
--   $$\sum_{t\in\mathcal T}\sum_{S\subseteq\mathcal J}\phi_{jt}(S)h_t(S)=\sum_{p\in\mathcal R_j}y_{jp}\ \ \forall j,\qquad \sum_{j\in\mathcal J}\sum_{p\in\mathcal R_j}a_{ip}y_{jp}\le c_i\ \ \forall i,$$
--   $$\sum_{S\subseteq\mathcal J}h_t(S)=1\ \ \forall t,\qquad h_t(S)\ge0,\quad y_{jp}\ge0.$$
--   This is a deterministic approximation of (2), in which the customers' choices take their expected values. It is the benchmark in the proof of the performance guarantee.
--
--   **Formalization Note** `zLP` is the supremum of the objective values. The milestone `FlexibleNRM.lp_feasible_bounded` says that it is attained.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (8), p.12

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- The constraints of **linear program (8)**:
`∑_t ∑_S φ_jt(S) h_t(S) = ∑_{p ∈ R_j} y_jp` for all `j`,
`∑_j ∑_{p ∈ R_j} a_ip y_jp ≤ c_i` for all `i`, `∑_S h_t(S) = 1` for all `t`, `h ≥ 0`, `y ≥ 0`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (8), p.12.

**Formalization Note** `h` and `y` are total functions; the values of `h` outside the periods
`Finset.Icc 1 T` and of `y j p` at `p ∉ R j` are neither constrained nor read. -/
structure LPFeasible {n m r : ℕ} (N : Network n m r) (h : ℕ → Finset (Fin n) → ℝ)
    (y : Fin n → Fin r → ℝ) : Prop where
  /-- Expected purchases equal expected route assignments. -/
  purchases : ∀ j, ∑ t ∈ Finset.Icc 1 N.T, ∑ S : Finset (Fin n), (N.φ t).prob S j * h t S =
    ∑ p ∈ N.R j, y j p
  /-- Expected route assignments respect the capacities. -/
  capacity : ∀ i, ∑ j, ∑ p ∈ N.R j, (N.a i p : ℝ) * y j p ≤ (N.c i : ℝ)
  /-- An assortment is offered with probability one. -/
  total : ∀ t ∈ Finset.Icc 1 N.T, ∑ S : Finset (Fin n), h t S = 1
  /-- `h_t(S) ≥ 0`. -/
  h_nonneg : ∀ t ∈ Finset.Icc 1 N.T, ∀ S, 0 ≤ h t S
  /-- `y_jp ≥ 0`. -/
  y_nonneg : ∀ j, ∀ p ∈ N.R j, 0 ≤ y j p

/-- The objective of (8), `∑_t ∑_S ∑_j f_j φ_jt(S) h_t(S)` (p.12). -/
noncomputable def lpObjective {n m r : ℕ} (N : Network n m r) (h : ℕ → Finset (Fin n) → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 N.T, ∑ S : Finset (Fin n), ∑ j, N.f j * (N.φ t).prob S j * h t S

/-- The set of objective values of the feasible solutions of (8). -/
def lpValues {n m r : ℕ} (N : Network n m r) : Set ℝ :=
  {v | ∃ h y, LPFeasible N h y ∧ v = lpObjective N h}

/-- `Z*_LP`, the optimal objective value of (8).

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (8), p.12.

**Formalization Note** (8) is printed with `max`; this is the `sSup` of the objective values. The
milestone `FlexibleNRM.lp_feasible_bounded` states that it is attained, so it is not a junk
value. -/
noncomputable def zLP {n m r : ℕ} (N : Network n m r) : ℝ :=
  sSup (lpValues N)

end FlexibleNRM


