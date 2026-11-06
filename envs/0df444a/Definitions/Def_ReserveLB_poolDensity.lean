-- Prove2me | Definitions.Def_ReserveLB_poolDensity
-- name    : ReserveLB_poolDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:30.11033+00:00
-- url     : https://prove2.me/theorems/c82797e0-6fc6-432e-a916-14966b057509
-- title:
--   Global density of a two-endpoint pool placement
-- statement:
--   Pools $p$ have $R_p$ endpoints of unit speed; original $j$ has a portion $z_{jp}$ in pool $p$, placed on two endpoints $u^1_{jp}, u^2_{jp}$ of that pool. The **global density** is
--   $$
--   \max_{\emptyset \ne A}\ \frac{1}{|A|}\sum_{(j,p):\ u^1_{jp}, u^2_{jp} \in A} z_{jp},
--   $$
--   over nonempty sets $A$ of endpoints of all pools: the largest ratio of trapped work to capacity.
--
--   **Formalization Note** Endpoints are pairs (pool, index); the value is $0$ when there are no endpoints.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 6.1, p.11; Section 2, p.3

import Mathlib

namespace ReserveLB

/-- **Global density of a two-endpoint pool placement.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 6.1, p.11: "Two independent uniform endpoints per original give expected global
density"; Section 2, p.3 (the fractional volume threshold).

Pools `p` have `R_p` unit endpoints; original `j` has portion `z_jp` in pool `p`, placed on the two
endpoints `u1_jp`, `u2_jp` of pool `p`. `poolDensity R z u1 u2` is the maximum, over nonempty sets
`A` of endpoints of all pools, of the total portion whose both endpoints lie in `A`, divided by
`|A|`.

**Formalization Note.** Endpoints are pairs `(p, a)` with `a < R_p`; portions are normalized
processing times, so every endpoint has unit speed. The value is `0` when there are no endpoints. -/
noncomputable def poolDensity {n : ℕ} {Pl : Type*} [Fintype Pl] [DecidableEq Pl] (R : Pl → ℕ)
    (z : Fin n → Pl → ℝ) (u1 u2 : Fin n → (p : Pl) → Fin (R p)) : ℝ :=
  if h : ((Finset.univ : Finset (Finset ((p : Pl) × Fin (R p)))).filter
      fun A => A.Nonempty).Nonempty then
    ((Finset.univ : Finset (Finset ((p : Pl) × Fin (R p)))).filter fun A => A.Nonempty).sup' h
      fun A => (∑ j, ∑ p, if (⟨p, u1 j p⟩ : (p : Pl) × Fin (R p)) ∈ A ∧ ⟨p, u2 j p⟩ ∈ A
        then z j p else 0) / A.card
  else 0

end ReserveLB


